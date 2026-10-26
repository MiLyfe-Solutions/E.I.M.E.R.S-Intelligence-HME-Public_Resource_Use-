import V185TrunkScan23Chunk0001

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_11856 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_11856 : Nat := 118140960795 + 11856 * 2 ^ 59
def prefixEnd_11856 : Nat := 4983230072969 + 3 ^ 40 * 11856 * 2
def baseEnd_11856 : Nat := 2029275546603615681827

theorem tailTrace_11856 : CollatzResearch.WordTrace tailWord_11856 prefixEnd_11856 2029275546603615681827 := by
  unfold tailWord_11856
  simp only [CollatzResearch.WordTrace]
  refine ⟨216211922527605844351711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 288282563370141125802281 216211922527605844351711)
  ·
    refine ⟨324317883791408766527567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216211922527605844351711 324317883791408766527567)
    ·
      refine ⟨486476825687113149791351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324317883791408766527567 486476825687113149791351)
      ·
        refine ⟨729715238530669724687027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486476825687113149791351 729715238530669724687027)
        ·
          refine ⟨1094572857796004587030541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 729715238530669724687027 1094572857796004587030541)
          ·
            refine ⟨410464821673501720136453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1094572857796004587030541 410464821673501720136453)
            ·
              refine ⟨76962154063781572525585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410464821673501720136453 76962154063781572525585)
              ·
                refine ⟨57721615547836179394189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76962154063781572525585 57721615547836179394189)
                ·
                  refine ⟨21645605830438567272821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57721615547836179394189 21645605830438567272821)
                  ·
                    refine ⟨2029275546603615681827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21645605830438567272821 2029275546603615681827)
                    ·
                      rfl

theorem cell23_11856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_11856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11856 prefixEnd_11856 := by exact prefixLift 11856
  have htrace : WordTrace (prefixWord ++ tailWord_11856) baseStart_11856 baseEnd_11856 := by
    simpa [prefixWord, tailWord_11856, baseEnd_11856] using wordTrace_append hprefix tailTrace_11856
  have hstable : (prefixWord ++ tailWord_11856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11856).length < 2 ^ (prefixWord ++ tailWord_11856).sum := by decide
  have hdescent : baseEnd_11856 < baseStart_11856 := by decide
  rcases family_descends (prefixWord ++ tailWord_11856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11913 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_11913 : Nat := 118140960795 + 11913 * 2 ^ 59
def prefixEnd_11913 : Nat := 4983230072969 + 3 ^ 40 * 11913 * 2
def baseEnd_11913 : Nat := 6117095037117124032719

theorem tailTrace_11913 : CollatzResearch.WordTrace tailWord_11913 prefixEnd_11913 6117095037117124032719 := by
  unfold tailWord_11913
  simp only [CollatzResearch.WordTrace]
  refine ⟨434502805848710423528393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 289668537232473615685595 434502805848710423528393)
  ·
    refine ⟨325877104386532817646295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 434502805848710423528393 325877104386532817646295)
    ·
      refine ⟨488815656579799226469443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 325877104386532817646295 488815656579799226469443)
      ·
        refine ⟨733223484869698839704165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488815656579799226469443 733223484869698839704165)
        ·
          refine ⟨137479403413068532444531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 733223484869698839704165 137479403413068532444531)
          ·
            refine ⟨206219105119602798666797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137479403413068532444531 206219105119602798666797)
            ·
              refine ⟨77332164419851049500049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206219105119602798666797 77332164419851049500049)
              ·
                refine ⟨57999123314888287125037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77332164419851049500049 57999123314888287125037)
                ·
                  refine ⟨21749671243083107671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57999123314888287125037 21749671243083107671889)
                  ·
                    refine ⟨16312253432312330753917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21749671243083107671889 16312253432312330753917)
                    ·
                      refine ⟨6117095037117124032719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 16312253432312330753917 6117095037117124032719)
                      ·
                        rfl

theorem cell23_11913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_11913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11913 prefixEnd_11913 := by exact prefixLift 11913
  have htrace : WordTrace (prefixWord ++ tailWord_11913) baseStart_11913 baseEnd_11913 := by
    simpa [prefixWord, tailWord_11913, baseEnd_11913] using wordTrace_append hprefix tailTrace_11913
  have hstable : (prefixWord ++ tailWord_11913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11913).length < 2 ^ (prefixWord ++ tailWord_11913).sum := by decide
  have hdescent : baseEnd_11913 < baseStart_11913 := by decide
  rcases family_descends (prefixWord ++ tailWord_11913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11927 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_11927 : Nat := 118140960795 + 11927 * 2 ^ 59
def prefixEnd_11927 : Nat := 4983230072969 + 3 ^ 40 * 11927 * 2
def baseEnd_11927 : Nat := 6124283766280069257655

theorem tailTrace_11927 : CollatzResearch.WordTrace tailWord_11927 prefixEnd_11927 6124283766280069257655 := by
  unfold tailWord_11927
  simp only [CollatzResearch.WordTrace]
  refine ⟨435013427797990814538035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 290008951865327209692023 435013427797990814538035)
  ·
    refine ⟨652520141696986221807053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 435013427797990814538035 652520141696986221807053)
    ·
      refine ⟨244695053136369833177645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 652520141696986221807053 244695053136369833177645)
      ·
        refine ⟨91760644926138687441617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244695053136369833177645 91760644926138687441617)
        ·
          refine ⟨68820483694604015581213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91760644926138687441617 68820483694604015581213)
          ·
            refine ⟨25807681385476505842955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68820483694604015581213 25807681385476505842955)
            ·
              refine ⟨38711522078214758764433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25807681385476505842955 38711522078214758764433)
              ·
                refine ⟨29033641558661069073325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38711522078214758764433 29033641558661069073325)
                ·
                  refine ⟨10887615584497900902497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29033641558661069073325 10887615584497900902497)
                  ·
                    refine ⟨8165711688373425676873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10887615584497900902497 8165711688373425676873)
                    ·
                      refine ⟨6124283766280069257655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8165711688373425676873 6124283766280069257655)
                      ·
                        rfl

theorem cell23_11927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_11927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11927 prefixEnd_11927 := by exact prefixLift 11927
  have htrace : WordTrace (prefixWord ++ tailWord_11927) baseStart_11927 baseEnd_11927 := by
    simpa [prefixWord, tailWord_11927, baseEnd_11927] using wordTrace_append hprefix tailTrace_11927
  have hstable : (prefixWord ++ tailWord_11927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11927).length < 2 ^ (prefixWord ++ tailWord_11927).sum := by decide
  have hdescent : baseEnd_11927 < baseStart_11927 := by decide
  rcases family_descends (prefixWord ++ tailWord_11927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11950 : List Nat := [4, 1, 4, 1, 2, 1, 10]
def baseStart_11950 : Nat := 118140960795 + 11950 * 2 ^ 59
def prefixEnd_11950 : Nat := 4983230072969 + 3 ^ 40 * 11950 * 2
def baseEnd_11950 : Nat := 75754244707820731729

theorem tailTrace_11950 : CollatzResearch.WordTrace tailWord_11950 prefixEnd_11950 75754244707820731729 := by
  unfold tailWord_11950
  simp only [CollatzResearch.WordTrace]
  refine ⟨54481538339333217828163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 290568204476443828416869 54481538339333217828163)
  ·
    refine ⟨81722307508999826742245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54481538339333217828163 81722307508999826742245)
    ·
      refine ⟨15322932657937467514171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81722307508999826742245 15322932657937467514171)
      ·
        refine ⟨22984398986906201271257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15322932657937467514171 22984398986906201271257)
        ·
          refine ⟨17238299240179650953443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22984398986906201271257 17238299240179650953443)
          ·
            refine ⟨25857448860269476430165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17238299240179650953443 25857448860269476430165)
            ·
              refine ⟨75754244707820731729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 25857448860269476430165 75754244707820731729)
              ·
                rfl

theorem cell23_11950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 10].length) (baseStart_11950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11950 prefixEnd_11950 := by exact prefixLift 11950
  have htrace : WordTrace (prefixWord ++ tailWord_11950) baseStart_11950 baseEnd_11950 := by
    simpa [prefixWord, tailWord_11950, baseEnd_11950] using wordTrace_append hprefix tailTrace_11950
  have hstable : (prefixWord ++ tailWord_11950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11950).length < 2 ^ (prefixWord ++ tailWord_11950).sum := by decide
  have hdescent : baseEnd_11950 < baseStart_11950 := by decide
  rcases family_descends (prefixWord ++ tailWord_11950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11974 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_11974 : Nat := 118140960795 + 11974 * 2 ^ 59
def prefixEnd_11974 : Nat := 4983230072969 + 3 ^ 40 * 11974 * 2
def baseEnd_11974 : Nat := 6148417357041385369939

theorem tailTrace_11974 : CollatzResearch.WordTrace tailWord_11974 prefixEnd_11974 6148417357041385369939 := by
  unfold tailWord_11974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647739332116182546843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 291151772418478560999317 13647739332116182546843)
  ·
    refine ⟨20471608998174273820265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647739332116182546843 20471608998174273820265)
    ·
      refine ⟨15353706748630705365199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20471608998174273820265 15353706748630705365199)
      ·
        refine ⟨23030560122946058047799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15353706748630705365199 23030560122946058047799)
        ·
          refine ⟨34545840184419087071699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23030560122946058047799 34545840184419087071699)
          ·
            refine ⟨51818760276628630607549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34545840184419087071699 51818760276628630607549)
            ·
              refine ⟨19432035103735736477831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51818760276628630607549 19432035103735736477831)
              ·
                refine ⟨29148052655603604716747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19432035103735736477831 29148052655603604716747)
                ·
                  refine ⟨43722078983405407075121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29148052655603604716747 43722078983405407075121)
                  ·
                    refine ⟨32791559237554055306341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43722078983405407075121 32791559237554055306341)
                    ·
                      refine ⟨6148417357041385369939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 32791559237554055306341 6148417357041385369939)
                      ·
                        rfl

theorem cell23_11974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_11974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_11974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_11974 prefixEnd_11974 := by exact prefixLift 11974
  have htrace : WordTrace (prefixWord ++ tailWord_11974) baseStart_11974 baseEnd_11974 := by
    simpa [prefixWord, tailWord_11974, baseEnd_11974] using wordTrace_append hprefix tailTrace_11974
  have hstable : (prefixWord ++ tailWord_11974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11974).length < 2 ^ (prefixWord ++ tailWord_11974).sum := by decide
  have hdescent : baseEnd_11974 < baseStart_11974 := by decide
  rcases family_descends (prefixWord ++ tailWord_11974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12000 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2]
def baseStart_12000 : Nat := 118140960795 + 12000 * 2 ^ 59
def prefixEnd_12000 : Nat := 4983230072969 + 3 ^ 40 * 12000 * 2
def baseEnd_12000 : Nat := 6161767854058283644819

theorem tailTrace_12000 : CollatzResearch.WordTrace tailWord_12000 prefixEnd_12000 6161767854058283644819 := by
  unfold tailWord_12000
  simp only [CollatzResearch.WordTrace]
  refine ⟨218837978266762140972727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291783971022349521296969 218837978266762140972727)
  ·
    refine ⟨328256967400143211459091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218837978266762140972727 328256967400143211459091)
    ·
      refine ⟨492385451100214817188637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328256967400143211459091 492385451100214817188637)
      ·
        refine ⟨184644544162580556445739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 492385451100214817188637 184644544162580556445739)
        ·
          refine ⟨276966816243870834668609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184644544162580556445739 276966816243870834668609)
          ·
            refine ⟨207725112182903126001457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276966816243870834668609 207725112182903126001457)
            ·
              refine ⟨155793834137177344501093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207725112182903126001457 155793834137177344501093)
              ·
                refine ⟨29211343900720752093955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155793834137177344501093 29211343900720752093955)
                ·
                  refine ⟨43817015851081128140933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29211343900720752093955 43817015851081128140933)
                  ·
                    refine ⟨8215690472077711526425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43817015851081128140933 8215690472077711526425)
                    ·
                      refine ⟨6161767854058283644819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8215690472077711526425 6161767854058283644819)
                      ·
                        rfl

theorem cell23_12000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_12000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12000 prefixEnd_12000 := by exact prefixLift 12000
  have htrace : WordTrace (prefixWord ++ tailWord_12000) baseStart_12000 baseEnd_12000 := by
    simpa [prefixWord, tailWord_12000, baseEnd_12000] using wordTrace_append hprefix tailTrace_12000
  have hstable : (prefixWord ++ tailWord_12000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12000).length < 2 ^ (prefixWord ++ tailWord_12000).sum := by decide
  have hdescent : baseEnd_12000 < baseStart_12000 := by decide
  rcases family_descends (prefixWord ++ tailWord_12000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12017 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_12017 : Nat := 118140960795 + 12017 * 2 ^ 59
def prefixEnd_12017 : Nat := 4983230072969 + 3 ^ 40 * 12017 * 2
def baseEnd_12017 : Nat := 6170497025184717132241

theorem tailTrace_12017 : CollatzResearch.WordTrace tailWord_12017 prefixEnd_12017 6170497025184717132241 := by
  unfold tailWord_12017
  simp only [CollatzResearch.WordTrace]
  refine ⟨438295997471936185314305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 292197331647957456876203 438295997471936185314305)
  ·
    refine ⟨328721998103952138985729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 438295997471936185314305 328721998103952138985729)
    ·
      refine ⟨246541498577964104239297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 328721998103952138985729 246541498577964104239297)
      ·
        refine ⟨184906123933473078179473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246541498577964104239297 184906123933473078179473)
        ·
          refine ⟨138679592950104808634605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184906123933473078179473 138679592950104808634605)
          ·
            refine ⟨52004847356289303237977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138679592950104808634605 52004847356289303237977)
            ·
              refine ⟨39003635517216977428483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52004847356289303237977 39003635517216977428483)
              ·
                refine ⟨58505453275825466142725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39003635517216977428483 58505453275825466142725)
                ·
                  refine ⟨10969772489217274901761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58505453275825466142725 10969772489217274901761)
                  ·
                    refine ⟨8227329366912956176321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10969772489217274901761 8227329366912956176321)
                    ·
                      refine ⟨6170497025184717132241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8227329366912956176321 6170497025184717132241)
                      ·
                        rfl

theorem cell23_12017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_12017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12017 prefixEnd_12017 := by exact prefixLift 12017
  have htrace : WordTrace (prefixWord ++ tailWord_12017) baseStart_12017 baseEnd_12017 := by
    simpa [prefixWord, tailWord_12017, baseEnd_12017] using wordTrace_append hprefix tailTrace_12017
  have hstable : (prefixWord ++ tailWord_12017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12017).length < 2 ^ (prefixWord ++ tailWord_12017).sum := by decide
  have hdescent : baseEnd_12017 < baseStart_12017 := by decide
  rcases family_descends (prefixWord ++ tailWord_12017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12023 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 7]
def baseStart_12023 : Nat := 118140960795 + 12023 * 2 ^ 59
def prefixEnd_12023 : Nat := 4983230072969 + 3 ^ 40 * 12023 * 2
def baseEnd_12023 : Nat := 685953101012410406357

theorem tailTrace_12023 : CollatzResearch.WordTrace tailWord_12023 prefixEnd_12023 685953101012410406357 := by
  unfold tailWord_12023
  simp only [CollatzResearch.WordTrace]
  refine ⟨438514835450199210032723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 292343223633466140021815 438514835450199210032723)
  ·
    refine ⟨657772253175298815049085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438514835450199210032723 657772253175298815049085)
    ·
      refine ⟨246664594940737055643407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 657772253175298815049085 246664594940737055643407)
      ·
        refine ⟨369996892411105583465111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246664594940737055643407 369996892411105583465111)
        ·
          refine ⟨554995338616658375197667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369996892411105583465111 554995338616658375197667)
          ·
            refine ⟨832493007924987562796501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554995338616658375197667 832493007924987562796501)
            ·
              refine ⟨19511554873241896003043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 832493007924987562796501 19511554873241896003043)
              ·
                refine ⟨29267332309862844004565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19511554873241896003043 29267332309862844004565)
                ·
                  refine ⟨685953101012410406357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 29267332309862844004565 685953101012410406357)
                  ·
                    rfl

theorem cell23_12023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 7].length) (baseStart_12023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12023 prefixEnd_12023 := by exact prefixLift 12023
  have htrace : WordTrace (prefixWord ++ tailWord_12023) baseStart_12023 baseEnd_12023 := by
    simpa [prefixWord, tailWord_12023, baseEnd_12023] using wordTrace_append hprefix tailTrace_12023
  have hstable : (prefixWord ++ tailWord_12023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12023).length < 2 ^ (prefixWord ++ tailWord_12023).sum := by decide
  have hdescent : baseEnd_12023 < baseStart_12023 := by decide
  rcases family_descends (prefixWord ++ tailWord_12023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12063 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_12063 : Nat := 118140960795 + 12063 * 2 ^ 59
def prefixEnd_12063 : Nat := 4983230072969 + 3 ^ 40 * 12063 * 2
def baseEnd_12063 : Nat := 6194117135291537157029

theorem tailTrace_12063 : CollatzResearch.WordTrace tailWord_12063 prefixEnd_12063 6194117135291537157029 := by
  unfold tailWord_12063
  simp only [CollatzResearch.WordTrace]
  refine ⟨439973755305286041488843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 293315836870190694325895 439973755305286041488843)
  ·
    refine ⟨659960632957929062233265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 439973755305286041488843 659960632957929062233265)
    ·
      refine ⟨494970474718446796674949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 659960632957929062233265 494970474718446796674949)
      ·
        refine ⟨92806964009708774376553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 494970474718446796674949 92806964009708774376553)
        ·
          refine ⟨69605223007281580782415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92806964009708774376553 69605223007281580782415)
          ·
            refine ⟨104407834510922371173623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69605223007281580782415 104407834510922371173623)
            ·
              refine ⟨156611751766383556760435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104407834510922371173623 156611751766383556760435)
              ·
                refine ⟨234917627649575335140653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156611751766383556760435 234917627649575335140653)
                ·
                  refine ⟨88094110368590750677745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 234917627649575335140653 88094110368590750677745)
                  ·
                    refine ⟨66070582776443063008309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88094110368590750677745 66070582776443063008309)
                    ·
                      refine ⟨6194117135291537157029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 66070582776443063008309 6194117135291537157029)
                      ·
                        rfl

theorem cell23_12063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_12063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12063 prefixEnd_12063 := by exact prefixLift 12063
  have htrace : WordTrace (prefixWord ++ tailWord_12063) baseStart_12063 baseEnd_12063 := by
    simpa [prefixWord, tailWord_12063, baseEnd_12063] using wordTrace_append hprefix tailTrace_12063
  have hstable : (prefixWord ++ tailWord_12063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12063).length < 2 ^ (prefixWord ++ tailWord_12063).sum := by decide
  have hdescent : baseEnd_12063 < baseStart_12063 := by decide
  rcases family_descends (prefixWord ++ tailWord_12063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12168 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 1, 4]
def baseStart_12168 : Nat := 118140960795 + 12168 * 2 ^ 59
def prefixEnd_12168 : Nat := 4983230072969 + 3 ^ 40 * 12168 * 2
def baseEnd_12168 : Nat := 2082677534671208781349

theorem tailTrace_12168 : CollatzResearch.WordTrace tailWord_12168 prefixEnd_12168 2082677534671208781349 := by
  unfold tailWord_12168
  simp only [CollatzResearch.WordTrace]
  refine ⟨221901709962444487030579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 295868946616592649374105 221901709962444487030579)
  ·
    refine ⟨332852564943666730545869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221901709962444487030579 332852564943666730545869)
    ·
      refine ⟨124819711853875023954701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332852564943666730545869 124819711853875023954701)
      ·
        refine ⟨46807391945203133983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124819711853875023954701 46807391945203133983013)
        ·
          refine ⟨8776385989725587621815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46807391945203133983013 8776385989725587621815)
          ·
            refine ⟨13164578984588381432723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776385989725587621815 13164578984588381432723)
            ·
              refine ⟨19746868476882572149085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13164578984588381432723 19746868476882572149085)
              ·
                refine ⟨7405075678830964555907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19746868476882572149085 7405075678830964555907)
                ·
                  refine ⟨11107613518246446833861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7405075678830964555907 11107613518246446833861)
                  ·
                    refine ⟨2082677534671208781349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11107613518246446833861 2082677534671208781349)
                    ·
                      rfl

theorem cell23_12168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_12168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12168 prefixEnd_12168 := by exact prefixLift 12168
  have htrace : WordTrace (prefixWord ++ tailWord_12168) baseStart_12168 baseEnd_12168 := by
    simpa [prefixWord, tailWord_12168, baseEnd_12168] using wordTrace_append hprefix tailTrace_12168
  have hstable : (prefixWord ++ tailWord_12168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12168).length < 2 ^ (prefixWord ++ tailWord_12168).sum := by decide
  have hdescent : baseEnd_12168 < baseStart_12168 := by decide
  rcases family_descends (prefixWord ++ tailWord_12168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12191 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_12191 : Nat := 118140960795 + 12191 * 2 ^ 59
def prefixEnd_12191 : Nat := 4983230072969 + 3 ^ 40 * 12191 * 2
def baseEnd_12191 : Nat := 6259842659067036356441

theorem tailTrace_12191 : CollatzResearch.WordTrace tailWord_12191 prefixEnd_12191 6259842659067036356441 := by
  unfold tailWord_12191
  simp only [CollatzResearch.WordTrace]
  refine ⟨444642298841563902148427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 296428199227709268098951 444642298841563902148427)
  ·
    refine ⟨666963448262345853222641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444642298841563902148427 666963448262345853222641)
    ·
      refine ⟨500222586196759389916981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666963448262345853222641 500222586196759389916981)
      ·
        refine ⟨46895867455946192804717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 500222586196759389916981 46895867455946192804717)
        ·
          refine ⟨17585950295979822301769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46895867455946192804717 17585950295979822301769)
          ·
            refine ⟨13189462721984866726327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17585950295979822301769 13189462721984866726327)
            ·
              refine ⟨19784194082977300089491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13189462721984866726327 19784194082977300089491)
              ·
                refine ⟨29676291124465950134237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19784194082977300089491 29676291124465950134237)
                ·
                  refine ⟨11128609171674731300339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29676291124465950134237 11128609171674731300339)
                  ·
                    refine ⟨16692913757512096950509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11128609171674731300339 16692913757512096950509)
                    ·
                      refine ⟨6259842659067036356441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 16692913757512096950509 6259842659067036356441)
                      ·
                        rfl

theorem cell23_12191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_12191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12191 prefixEnd_12191 := by exact prefixLift 12191
  have htrace : WordTrace (prefixWord ++ tailWord_12191) baseStart_12191 baseEnd_12191 := by
    simpa [prefixWord, tailWord_12191, baseEnd_12191] using wordTrace_append hprefix tailTrace_12191
  have hstable : (prefixWord ++ tailWord_12191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12191).length < 2 ^ (prefixWord ++ tailWord_12191).sum := by decide
  have hdescent : baseEnd_12191 < baseStart_12191 := by decide
  rcases family_descends (prefixWord ++ tailWord_12191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12207 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 2, 4]
def baseStart_12207 : Nat := 118140960795 + 12207 * 2 ^ 59
def prefixEnd_12207 : Nat := 4983230072969 + 3 ^ 40 * 12207 * 2
def baseEnd_12207 : Nat := 2089352783179657918789

theorem tailTrace_12207 : CollatzResearch.WordTrace tailWord_12207 prefixEnd_12207 2089352783179657918789 := by
  unfold tailWord_12207
  simp only [CollatzResearch.WordTrace]
  refine ⟨445225866783598634730875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 296817244522399089820583 445225866783598634730875)
  ·
    refine ⟨667838800175397952096313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445225866783598634730875 667838800175397952096313)
    ·
      refine ⟨500879100131548464072235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 667838800175397952096313 500879100131548464072235)
      ·
        refine ⟨751318650197322696108353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500879100131548464072235 751318650197322696108353)
        ·
          refine ⟨563488987647992022081265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751318650197322696108353 563488987647992022081265)
          ·
            refine ⟨422616740735994016560949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563488987647992022081265 422616740735994016560949)
            ·
              refine ⟨39620319443999439052589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422616740735994016560949 39620319443999439052589)
              ·
                refine ⟨14857619791499789644721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39620319443999439052589 14857619791499789644721)
                ·
                  refine ⟨11143214843624842233541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857619791499789644721 11143214843624842233541)
                  ·
                    refine ⟨2089352783179657918789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11143214843624842233541 2089352783179657918789)
                    ·
                      rfl

theorem cell23_12207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_12207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12207 prefixEnd_12207 := by exact prefixLift 12207
  have htrace : WordTrace (prefixWord ++ tailWord_12207) baseStart_12207 baseEnd_12207 := by
    simpa [prefixWord, tailWord_12207, baseEnd_12207] using wordTrace_append hprefix tailTrace_12207
  have hstable : (prefixWord ++ tailWord_12207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12207).length < 2 ^ (prefixWord ++ tailWord_12207).sum := by decide
  have hdescent : baseEnd_12207 < baseStart_12207 := by decide
  rcases family_descends (prefixWord ++ tailWord_12207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12210 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_12210 : Nat := 118140960795 + 12210 * 2 ^ 59
def prefixEnd_12210 : Nat := 4983230072969 + 3 ^ 40 * 12210 * 2
def baseEnd_12210 : Nat := 6269598791502462018853

theorem tailTrace_12210 : CollatzResearch.WordTrace tailWord_12210 prefixEnd_12210 6269598791502462018853 := by
  unfold tailWord_12210
  simp only [CollatzResearch.WordTrace]
  refine ⟨111333821443182536772521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 296890190515153431393389 111333821443182536772521)
  ·
    refine ⟨83500366082386902579391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111333821443182536772521 83500366082386902579391)
    ·
      refine ⟨125250549123580353869087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83500366082386902579391 125250549123580353869087)
      ·
        refine ⟨187875823685370530803631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125250549123580353869087 187875823685370530803631)
        ·
          refine ⟨281813735528055796205447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187875823685370530803631 281813735528055796205447)
          ·
            refine ⟨422720603292083694308171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281813735528055796205447 422720603292083694308171)
            ·
              refine ⟨634080904938125541462257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422720603292083694308171 634080904938125541462257)
              ·
                refine ⟨475560678703594156096693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634080904938125541462257 475560678703594156096693)
                ·
                  refine ⟨44583813628461952134065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 475560678703594156096693 44583813628461952134065)
                  ·
                    refine ⟨33437860221346464100549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44583813628461952134065 33437860221346464100549)
                    ·
                      refine ⟨6269598791502462018853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 33437860221346464100549 6269598791502462018853)
                      ·
                        rfl

theorem cell23_12210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_12210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12210 prefixEnd_12210 := by exact prefixLift 12210
  have htrace : WordTrace (prefixWord ++ tailWord_12210) baseStart_12210 baseEnd_12210 := by
    simpa [prefixWord, tailWord_12210, baseEnd_12210] using wordTrace_append hprefix tailTrace_12210
  have hstable : (prefixWord ++ tailWord_12210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12210).length < 2 ^ (prefixWord ++ tailWord_12210).sum := by decide
  have hdescent : baseEnd_12210 < baseStart_12210 := by decide
  rcases family_descends (prefixWord ++ tailWord_12210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12217 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_12217 : Nat := 118140960795 + 12217 * 2 ^ 59
def prefixEnd_12217 : Nat := 4983230072969 + 3 ^ 40 * 12217 * 2
def baseEnd_12217 : Nat := 6273193156083934631321

theorem tailTrace_12217 : CollatzResearch.WordTrace tailWord_12217 prefixEnd_12217 6273193156083934631321 := by
  unfold tailWord_12217
  simp only [CollatzResearch.WordTrace]
  refine ⟨445590596747370342594905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297060397831580228396603 445590596747370342594905)
  ·
    refine ⟨334192947560527756946179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 445590596747370342594905 334192947560527756946179)
    ·
      refine ⟨501289421340791635419269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334192947560527756946179 501289421340791635419269)
      ·
        refine ⟨93991766501398431641113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 501289421340791635419269 93991766501398431641113)
        ·
          refine ⟨70493824876048823730835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93991766501398431641113 70493824876048823730835)
          ·
            refine ⟨105740737314073235596253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70493824876048823730835 105740737314073235596253)
            ·
              refine ⟨39652776492777463348595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105740737314073235596253 39652776492777463348595)
              ·
                refine ⟨59479164739166195022893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39652776492777463348595 59479164739166195022893)
                ·
                  refine ⟨22304686777187323133585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59479164739166195022893 22304686777187323133585)
                  ·
                    refine ⟨16728515082890492350189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22304686777187323133585 16728515082890492350189)
                    ·
                      refine ⟨6273193156083934631321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 16728515082890492350189 6273193156083934631321)
                      ·
                        rfl

theorem cell23_12217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_12217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12217 prefixEnd_12217 := by exact prefixLift 12217
  have htrace : WordTrace (prefixWord ++ tailWord_12217) baseStart_12217 baseEnd_12217 := by
    simpa [prefixWord, tailWord_12217, baseEnd_12217] using wordTrace_append hprefix tailTrace_12217
  have hstable : (prefixWord ++ tailWord_12217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12217).length < 2 ^ (prefixWord ++ tailWord_12217).sum := by decide
  have hdescent : baseEnd_12217 < baseStart_12217 := by decide
  rcases family_descends (prefixWord ++ tailWord_12217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12231 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_12231 : Nat := 118140960795 + 12231 * 2 ^ 59
def prefixEnd_12231 : Nat := 4983230072969 + 3 ^ 40 * 12231 * 2
def baseEnd_12231 : Nat := 6280381885246879856257

theorem tailTrace_12231 : CollatzResearch.WordTrace tailWord_12231 prefixEnd_12231 6280381885246879856257 := by
  unfold tailWord_12231
  simp only [CollatzResearch.WordTrace]
  refine ⟨446101218696650733604547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297400812464433822403031 446101218696650733604547)
  ·
    refine ⟨669151828044976100406821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 446101218696650733604547 669151828044976100406821)
    ·
      refine ⟨125465967758433018826279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 669151828044976100406821 125465967758433018826279)
      ·
        refine ⟨188198951637649528239419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125465967758433018826279 188198951637649528239419)
        ·
          refine ⟨282298427456474292359129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188198951637649528239419 282298427456474292359129)
          ·
            refine ⟨211723820592355719269347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282298427456474292359129 211723820592355719269347)
            ·
              refine ⟨317585730888533578904021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211723820592355719269347 317585730888533578904021)
              ·
                refine ⟨7443415567700005755563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 317585730888533578904021 7443415567700005755563)
                ·
                  refine ⟨11165123351550008633345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7443415567700005755563 11165123351550008633345)
                  ·
                    refine ⟨8373842513662506475009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11165123351550008633345 8373842513662506475009)
                    ·
                      refine ⟨6280381885246879856257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8373842513662506475009 6280381885246879856257)
                      ·
                        rfl

theorem cell23_12231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_12231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12231 prefixEnd_12231 := by exact prefixLift 12231
  have htrace : WordTrace (prefixWord ++ tailWord_12231) baseStart_12231 baseEnd_12231 := by
    simpa [prefixWord, tailWord_12231, baseEnd_12231] using wordTrace_append hprefix tailTrace_12231
  have hstable : (prefixWord ++ tailWord_12231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12231).length < 2 ^ (prefixWord ++ tailWord_12231).sum := by decide
  have hdescent : baseEnd_12231 < baseStart_12231 := by decide
  rcases family_descends (prefixWord ++ tailWord_12231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12237 : List Nat := [1, 6, 3, 13]
def baseStart_12237 : Nat := 118140960795 + 12237 * 2 ^ 59
def prefixEnd_12237 : Nat := 4983230072969 + 3 ^ 40 * 12237 * 2
def baseEnd_12237 : Nat := 2873096830897968167

theorem tailTrace_12237 : CollatzResearch.WordTrace tailWord_12237 prefixEnd_12237 2873096830897968167 := by
  unfold tailWord_12237
  simp only [CollatzResearch.WordTrace]
  refine ⟨446320056674913758322965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297546704449942505548643 446320056674913758322965)
  ·
    refine ⟨20921252656636582421389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 446320056674913758322965 20921252656636582421389)
    ·
      refine ⟨7845469746238718408021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20921252656636582421389 7845469746238718408021)
      ·
        refine ⟨2873096830897968167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 7845469746238718408021 2873096830897968167)
        ·
          rfl

theorem cell23_12237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 13].length) (baseStart_12237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12237 prefixEnd_12237 := by exact prefixLift 12237
  have htrace : WordTrace (prefixWord ++ tailWord_12237) baseStart_12237 baseEnd_12237 := by
    simpa [prefixWord, tailWord_12237, baseEnd_12237] using wordTrace_append hprefix tailTrace_12237
  have hstable : (prefixWord ++ tailWord_12237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12237).length < 2 ^ (prefixWord ++ tailWord_12237).sum := by decide
  have hdescent : baseEnd_12237 < baseStart_12237 := by decide
  rcases family_descends (prefixWord ++ tailWord_12237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12242 : List Nat := [3, 2, 2, 3, 3, 1, 2, 2, 1, 1, 3]
def baseStart_12242 : Nat := 118140960795 + 12242 * 2 ^ 59
def prefixEnd_12242 : Nat := 4983230072969 + 3 ^ 40 * 12242 * 2
def baseEnd_12242 : Nat := 6286030172446336818707

theorem tailTrace_12242 : CollatzResearch.WordTrace tailWord_12242 prefixEnd_12242 6286030172446336818707 := by
  unfold tailWord_12242
  simp only [CollatzResearch.WordTrace]
  refine ⟨111625605414199903063745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 297668281104533074836653 111625605414199903063745)
  ·
    refine ⟨83719204060649927297809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111625605414199903063745 83719204060649927297809)
    ·
      refine ⟨62789403045487445473357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83719204060649927297809 62789403045487445473357)
      ·
        refine ⟨23546026142057792052509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62789403045487445473357 23546026142057792052509)
        ·
          refine ⟨8829759803271672019691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23546026142057792052509 8829759803271672019691)
          ·
            refine ⟨13244639704907508029537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829759803271672019691 13244639704907508029537)
            ·
              refine ⟨9933479778680631022153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13244639704907508029537 9933479778680631022153)
              ·
                refine ⟨7450109834010473266615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9933479778680631022153 7450109834010473266615)
                ·
                  refine ⟨11175164751015709899923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7450109834010473266615 11175164751015709899923)
                  ·
                    refine ⟨16762747126523564849885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11175164751015709899923 16762747126523564849885)
                    ·
                      refine ⟨6286030172446336818707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 16762747126523564849885 6286030172446336818707)
                      ·
                        rfl

theorem cell23_12242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_12242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12242 prefixEnd_12242 := by exact prefixLift 12242
  have htrace : WordTrace (prefixWord ++ tailWord_12242) baseStart_12242 baseEnd_12242 := by
    simpa [prefixWord, tailWord_12242, baseEnd_12242] using wordTrace_append hprefix tailTrace_12242
  have hstable : (prefixWord ++ tailWord_12242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12242).length < 2 ^ (prefixWord ++ tailWord_12242).sum := by decide
  have hdescent : baseEnd_12242 < baseStart_12242 := by decide
  rcases family_descends (prefixWord ++ tailWord_12242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12298 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_12298 : Nat := 118140960795 + 12298 * 2 ^ 59
def prefixEnd_12298 : Nat := 4983230072969 + 3 ^ 40 * 12298 * 2
def baseEnd_12298 : Nat := 6314785089098117718449

theorem tailTrace_12298 : CollatzResearch.WordTrace tailWord_12298 prefixEnd_12298 6314785089098117718449 := by
  unfold tailWord_12298
  simp only [CollatzResearch.WordTrace]
  refine ⟨112136227363480294073387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 299029939635947450862365 112136227363480294073387)
  ·
    refine ⟨168204341045220441110081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112136227363480294073387 168204341045220441110081)
    ·
      refine ⟨126153255783915330832561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168204341045220441110081 126153255783915330832561)
      ·
        refine ⟨94614941837936498124421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126153255783915330832561 94614941837936498124421)
        ·
          refine ⟨17740301594613093398329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94614941837936498124421 17740301594613093398329)
          ·
            refine ⟨13305226195959820048747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17740301594613093398329 13305226195959820048747)
            ·
              refine ⟨19957839293939730073121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305226195959820048747 19957839293939730073121)
              ·
                refine ⟨14968379470454797554841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19957839293939730073121 14968379470454797554841)
                ·
                  refine ⟨11226284602841098166131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14968379470454797554841 11226284602841098166131)
                  ·
                    refine ⟨16839426904261647249197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11226284602841098166131 16839426904261647249197)
                    ·
                      refine ⟨6314785089098117718449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 16839426904261647249197 6314785089098117718449)
                      ·
                        rfl

theorem cell23_12298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_12298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12298 prefixEnd_12298 := by exact prefixLift 12298
  have htrace : WordTrace (prefixWord ++ tailWord_12298) baseStart_12298 baseEnd_12298 := by
    simpa [prefixWord, tailWord_12298, baseEnd_12298] using wordTrace_append hprefix tailTrace_12298
  have hstable : (prefixWord ++ tailWord_12298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12298).length < 2 ^ (prefixWord ++ tailWord_12298).sum := by decide
  have hdescent : baseEnd_12298 < baseStart_12298 := by decide
  rcases family_descends (prefixWord ++ tailWord_12298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2]
def baseStart_12304 : Nat := 118140960795 + 12304 * 2 ^ 59
def prefixEnd_12304 : Nat := 4983230072969 + 3 ^ 40 * 12304 * 2
def baseEnd_12304 : Nat := 6317865973025094243421

theorem tailTrace_12304 : CollatzResearch.WordTrace tailWord_12304 prefixEnd_12304 6317865973025094243421 := by
  unfold tailWord_12304
  simp only [CollatzResearch.WordTrace]
  refine ⟨224381873716092100505983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 299175831621456134007977 224381873716092100505983)
  ·
    refine ⟨336572810574138150758975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224381873716092100505983 336572810574138150758975)
    ·
      refine ⟨504859215861207226138463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336572810574138150758975 504859215861207226138463)
      ·
        refine ⟨757288823791810839207695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504859215861207226138463 757288823791810839207695)
        ·
          refine ⟨1135933235687716258811543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757288823791810839207695 1135933235687716258811543)
          ·
            refine ⟨1703899853531574388217315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135933235687716258811543 1703899853531574388217315)
            ·
              refine ⟨2555849780297361582325973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703899853531574388217315 2555849780297361582325973)
              ·
                refine ⟨59902729225719412085765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2555849780297361582325973 59902729225719412085765)
                ·
                  refine ⟨11231761729822389766081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59902729225719412085765 11231761729822389766081)
                  ·
                    refine ⟨8423821297366792324561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11231761729822389766081 8423821297366792324561)
                    ·
                      refine ⟨6317865973025094243421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8423821297366792324561 6317865973025094243421)
                      ·
                        rfl

theorem cell23_12304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2].length) (baseStart_12304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12304 prefixEnd_12304 := by exact prefixLift 12304
  have htrace : WordTrace (prefixWord ++ tailWord_12304) baseStart_12304 baseEnd_12304 := by
    simpa [prefixWord, tailWord_12304, baseEnd_12304] using wordTrace_append hprefix tailTrace_12304
  have hstable : (prefixWord ++ tailWord_12304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12304).length < 2 ^ (prefixWord ++ tailWord_12304).sum := by decide
  have hdescent : baseEnd_12304 < baseStart_12304 := by decide
  rcases family_descends (prefixWord ++ tailWord_12304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12377 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_12377 : Nat := 118140960795 + 12377 * 2 ^ 59
def prefixEnd_12377 : Nat := 4983230072969 + 3 ^ 40 * 12377 * 2
def baseEnd_12377 : Nat := 6355350060803308630585

theorem tailTrace_12377 : CollatzResearch.WordTrace tailWord_12377 prefixEnd_12377 6355350060803308630585 := by
  unfold tailWord_12377
  simp only [CollatzResearch.WordTrace]
  refine ⟨451426276167717668419385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 300950850778478445612923 451426276167717668419385)
  ·
    refine ⟨338569707125788251314539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 451426276167717668419385 338569707125788251314539)
    ·
      refine ⟨507854560688682376971809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338569707125788251314539 507854560688682376971809)
      ·
        refine ⟨380890920516511782728857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507854560688682376971809 380890920516511782728857)
        ·
          refine ⟨285668190387383837046643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380890920516511782728857 285668190387383837046643)
          ·
            refine ⟨428502285581075755569965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285668190387383837046643 428502285581075755569965)
            ·
              refine ⟨160688357092903408338737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428502285581075755569965 160688357092903408338737)
              ·
                refine ⟨120516267819677556254053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160688357092903408338737 120516267819677556254053)
                ·
                  refine ⟨22596800216189541797635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120516267819677556254053 22596800216189541797635)
                  ·
                    refine ⟨33895200324284312696453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22596800216189541797635 33895200324284312696453)
                    ·
                      refine ⟨6355350060803308630585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 33895200324284312696453 6355350060803308630585)
                      ·
                        rfl

theorem cell23_12377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_12377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12377 prefixEnd_12377 := by exact prefixLift 12377
  have htrace : WordTrace (prefixWord ++ tailWord_12377) baseStart_12377 baseEnd_12377 := by
    simpa [prefixWord, tailWord_12377, baseEnd_12377] using wordTrace_append hprefix tailTrace_12377
  have hstable : (prefixWord ++ tailWord_12377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12377).length < 2 ^ (prefixWord ++ tailWord_12377).sum := by decide
  have hdescent : baseEnd_12377 < baseStart_12377 := by decide
  rcases family_descends (prefixWord ++ tailWord_12377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12427 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3]
def baseStart_12427 : Nat := 118140960795 + 12427 * 2 ^ 59
def prefixEnd_12427 : Nat := 4983230072969 + 3 ^ 40 * 12427 * 2
def baseEnd_12427 : Nat := 6381024093528113005355

theorem tailTrace_12427 : CollatzResearch.WordTrace tailWord_12427 prefixEnd_12427 6381024093528113005355 := by
  unfold tailWord_12427
  simp only [CollatzResearch.WordTrace]
  refine ⟨453249925986576207739535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 302166617324384138493023 453249925986576207739535)
  ·
    refine ⟨679874888979864311609303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 453249925986576207739535 679874888979864311609303)
    ·
      refine ⟨1019812333469796467413955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679874888979864311609303 1019812333469796467413955)
      ·
        refine ⟨1529718500204694701120933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019812333469796467413955 1529718500204694701120933)
        ·
          refine ⟨286822218788380256460175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1529718500204694701120933 286822218788380256460175)
          ·
            refine ⟨430233328182570384690263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286822218788380256460175 430233328182570384690263)
            ·
              refine ⟨645349992273855577035395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430233328182570384690263 645349992273855577035395)
              ·
                refine ⟨968024988410783365553093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645349992273855577035395 968024988410783365553093)
                ·
                  refine ⟨181504685327021881041205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968024988410783365553093 181504685327021881041205)
                  ·
                    refine ⟨17016064249408301347613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181504685327021881041205 17016064249408301347613)
                    ·
                      refine ⟨6381024093528113005355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 17016064249408301347613 6381024093528113005355)
                      ·
                        rfl

theorem cell23_12427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 5, 3].length) (baseStart_12427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12427 prefixEnd_12427 := by exact prefixLift 12427
  have htrace : WordTrace (prefixWord ++ tailWord_12427) baseStart_12427 baseEnd_12427 := by
    simpa [prefixWord, tailWord_12427, baseEnd_12427] using wordTrace_append hprefix tailTrace_12427
  have hstable : (prefixWord ++ tailWord_12427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12427).length < 2 ^ (prefixWord ++ tailWord_12427).sum := by decide
  have hdescent : baseEnd_12427 < baseStart_12427 := by decide
  rcases family_descends (prefixWord ++ tailWord_12427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12434 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_12434 : Nat := 118140960795 + 12434 * 2 ^ 59
def prefixEnd_12434 : Nat := 4983230072969 + 3 ^ 40 * 12434 * 2
def baseEnd_12434 : Nat := 709402050901065068647

theorem tailTrace_12434 : CollatzResearch.WordTrace tailWord_12434 prefixEnd_12434 709402050901065068647 := by
  unfold tailWord_12434
  simp only [CollatzResearch.WordTrace]
  refine ⟨113376309240304100811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 302336824640810935496237 113376309240304100811089)
  ·
    refine ⟨85032231930228075608317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113376309240304100811089 85032231930228075608317)
    ·
      refine ⟨31887086973835528353119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85032231930228075608317 31887086973835528353119)
      ·
        refine ⟨47830630460753292529679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31887086973835528353119 47830630460753292529679)
        ·
          refine ⟨71745945691129938794519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47830630460753292529679 71745945691129938794519)
          ·
            refine ⟨107618918536694908191779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71745945691129938794519 107618918536694908191779)
            ·
              refine ⟨161428377805042362287669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107618918536694908191779 161428377805042362287669)
              ·
                refine ⟨15133910419222721464469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161428377805042362287669 15133910419222721464469)
                ·
                  refine ⟨709402050901065068647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15133910419222721464469 709402050901065068647)
                  ·
                    rfl

theorem cell23_12434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_12434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12434 prefixEnd_12434 := by exact prefixLift 12434
  have htrace : WordTrace (prefixWord ++ tailWord_12434) baseStart_12434 baseEnd_12434 := by
    simpa [prefixWord, tailWord_12434, baseEnd_12434] using wordTrace_append hprefix tailTrace_12434
  have hstable : (prefixWord ++ tailWord_12434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12434).length < 2 ^ (prefixWord ++ tailWord_12434).sum := by decide
  have hdescent : baseEnd_12434 < baseStart_12434 := by decide
  rcases family_descends (prefixWord ++ tailWord_12434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12455 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 1, 4]
def baseStart_12455 : Nat := 118140960795 + 12455 * 2 ^ 59
def prefixEnd_12455 : Nat := 4983230072969 + 3 ^ 40 * 12455 * 2
def baseEnd_12455 : Nat := 2131800517284667818409

theorem tailTrace_12455 : CollatzResearch.WordTrace tailWord_12455 prefixEnd_12455 2131800517284667818409 := by
  unfold tailWord_12455
  simp only [CollatzResearch.WordTrace]
  refine ⟨454271169885136989758819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 302847446590091326505879 454271169885136989758819)
  ·
    refine ⟨681406754827705484638229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454271169885136989758819 681406754827705484638229)
    ·
      refine ⟨31940941632548694592417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 681406754827705484638229 31940941632548694592417)
      ·
        refine ⟨23955706224411520944313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31940941632548694592417 23955706224411520944313)
        ·
          refine ⟨17966779668308640708235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23955706224411520944313 17966779668308640708235)
          ·
            refine ⟨26950169502462961062353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17966779668308640708235 26950169502462961062353)
            ·
              refine ⟨20212627126847220796765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26950169502462961062353 20212627126847220796765)
              ·
                refine ⟨7579735172567707798787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20212627126847220796765 7579735172567707798787)
                ·
                  refine ⟨11369602758851561698181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7579735172567707798787 11369602758851561698181)
                  ·
                    refine ⟨2131800517284667818409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11369602758851561698181 2131800517284667818409)
                    ·
                      rfl

theorem cell23_12455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_12455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12455 prefixEnd_12455 := by exact prefixLift 12455
  have htrace : WordTrace (prefixWord ++ tailWord_12455) baseStart_12455 baseEnd_12455 := by
    simpa [prefixWord, tailWord_12455, baseEnd_12455] using wordTrace_append hprefix tailTrace_12455
  have hstable : (prefixWord ++ tailWord_12455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12455).length < 2 ^ (prefixWord ++ tailWord_12455).sum := by decide
  have hdescent : baseEnd_12455 < baseStart_12455 := by decide
  rcases family_descends (prefixWord ++ tailWord_12455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12586 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_12586 : Nat := 118140960795 + 12586 * 2 ^ 59
def prefixEnd_12586 : Nat := 4983230072969 + 3 ^ 40 * 12586 * 2
def baseEnd_12586 : Nat := 6462667517592990917125

theorem tailTrace_12586 : CollatzResearch.WordTrace tailWord_12586 prefixEnd_12586 6462667517592990917125 := by
  unfold tailWord_12586
  simp only [CollatzResearch.WordTrace]
  refine ⟨114762283102636590694403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 306032754940364241851741 114762283102636590694403)
  ·
    refine ⟨172143424653954886041605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114762283102636590694403 172143424653954886041605)
    ·
      refine ⟨32276892122616541132801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172143424653954886041605 32276892122616541132801)
      ·
        refine ⟨24207669091962405849601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32276892122616541132801 24207669091962405849601)
        ·
          refine ⟨18155751818971804387201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24207669091962405849601 18155751818971804387201)
          ·
            refine ⟨13616813864228853290401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18155751818971804387201 13616813864228853290401)
            ·
              refine ⟨10212610398171639967801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13616813864228853290401 10212610398171639967801)
              ·
                refine ⟨7659457798628729975851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10212610398171639967801 7659457798628729975851)
                ·
                  refine ⟨11489186697943094963777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7659457798628729975851 11489186697943094963777)
                  ·
                    refine ⟨8616890023457321222833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11489186697943094963777 8616890023457321222833)
                    ·
                      refine ⟨6462667517592990917125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8616890023457321222833 6462667517592990917125)
                      ·
                        rfl

theorem cell23_12586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_12586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12586 prefixEnd_12586 := by exact prefixLift 12586
  have htrace : WordTrace (prefixWord ++ tailWord_12586) baseStart_12586 baseEnd_12586 := by
    simpa [prefixWord, tailWord_12586, baseEnd_12586] using wordTrace_append hprefix tailTrace_12586
  have hstable : (prefixWord ++ tailWord_12586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12586).length < 2 ^ (prefixWord ++ tailWord_12586).sum := by decide
  have hdescent : baseEnd_12586 < baseStart_12586 := by decide
  rcases family_descends (prefixWord ++ tailWord_12586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12601 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 2, 6]
def baseStart_12601 : Nat := 118140960795 + 12601 * 2 ^ 59
def prefixEnd_12601 : Nat := 4983230072969 + 3 ^ 40 * 12601 * 2
def baseEnd_12601 : Nat := 2156789909136810743185

theorem tailTrace_12601 : CollatzResearch.WordTrace tailWord_12601 prefixEnd_12601 2156789909136810743185 := by
  unfold tailWord_12601
  simp only [CollatzResearch.WordTrace]
  refine ⟨459596227356203924573657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 306397484904135949715771 459596227356203924573657)
  ·
    refine ⟨344697170517152943430243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 459596227356203924573657 344697170517152943430243)
    ·
      refine ⟨517045755775729415145365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344697170517152943430243 517045755775729415145365)
      ·
        refine ⟨24236519801987316334939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 517045755775729415145365 24236519801987316334939)
        ·
          refine ⟨36354779702980974502409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24236519801987316334939 36354779702980974502409)
          ·
            refine ⟨27266084777235730876807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36354779702980974502409 27266084777235730876807)
            ·
              refine ⟨40899127165853596315211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27266084777235730876807 40899127165853596315211)
              ·
                refine ⟨61348690748780394472817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40899127165853596315211 61348690748780394472817)
                ·
                  refine ⟨46011518061585295854613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61348690748780394472817 46011518061585295854613)
                  ·
                    refine ⟨2156789909136810743185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46011518061585295854613 2156789909136810743185)
                    ·
                      rfl

theorem cell23_12601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_12601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12601 prefixEnd_12601 := by exact prefixLift 12601
  have htrace : WordTrace (prefixWord ++ tailWord_12601) baseStart_12601 baseEnd_12601 := by
    simpa [prefixWord, tailWord_12601, baseEnd_12601] using wordTrace_append hprefix tailTrace_12601
  have hstable : (prefixWord ++ tailWord_12601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12601).length < 2 ^ (prefixWord ++ tailWord_12601).sum := by decide
  have hdescent : baseEnd_12601 < baseStart_12601 := by decide
  rcases family_descends (prefixWord ++ tailWord_12601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12629 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_12629 : Nat := 118140960795 + 12629 * 2 ^ 59
def prefixEnd_12629 : Nat := 4983230072969 + 3 ^ 40 * 12629 * 2
def baseEnd_12629 : Nat := 6484747185736322679427

theorem tailTrace_12629 : CollatzResearch.WordTrace tailWord_12629 prefixEnd_12629 6484747185736322679427 := by
  unfold tailWord_12629
  simp only [CollatzResearch.WordTrace]
  refine ⟨460617471254764706592941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 307078314169843137728627 460617471254764706592941)
  ·
    refine ⟨172731551720536764972353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 460617471254764706592941 172731551720536764972353)
    ·
      refine ⟨129548663790402573729265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172731551720536764972353 129548663790402573729265)
      ·
        refine ⟨97161497842801930296949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129548663790402573729265 97161497842801930296949)
        ·
          refine ⟨9108890422762680965339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97161497842801930296949 9108890422762680965339)
          ·
            refine ⟨13663335634144021448009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108890422762680965339 13663335634144021448009)
            ·
              refine ⟨10247501725608016086007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13663335634144021448009 10247501725608016086007)
              ·
                refine ⟨15371252588412024129011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247501725608016086007 15371252588412024129011)
                ·
                  refine ⟨23056878882618036193517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15371252588412024129011 23056878882618036193517)
                  ·
                    refine ⟨8646329580981763572569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23056878882618036193517 8646329580981763572569)
                    ·
                      refine ⟨6484747185736322679427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8646329580981763572569 6484747185736322679427)
                      ·
                        rfl

theorem cell23_12629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_12629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12629 prefixEnd_12629 := by exact prefixLift 12629
  have htrace : WordTrace (prefixWord ++ tailWord_12629) baseStart_12629 baseEnd_12629 := by
    simpa [prefixWord, tailWord_12629, baseEnd_12629] using wordTrace_append hprefix tailTrace_12629
  have hstable : (prefixWord ++ tailWord_12629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12629).length < 2 ^ (prefixWord ++ tailWord_12629).sum := by decide
  have hdescent : baseEnd_12629 < baseStart_12629 := by decide
  rcases family_descends (prefixWord ++ tailWord_12629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12642 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_12642 : Nat := 118140960795 + 12642 * 2 ^ 59
def prefixEnd_12642 : Nat := 4983230072969 + 3 ^ 40 * 12642 * 2
def baseEnd_12642 : Nat := 6491422434244771816867

theorem tailTrace_12642 : CollatzResearch.WordTrace tailWord_12642 prefixEnd_12642 6491422434244771816867 := by
  unfold tailWord_12642
  simp only [CollatzResearch.WordTrace]
  refine ⟨115272905051916981704045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 307394413471778617877453 115272905051916981704045)
  ·
    refine ⟨43227339394468868139017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115272905051916981704045 43227339394468868139017)
    ·
      refine ⟨32420504545851651104263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43227339394468868139017 32420504545851651104263)
      ·
        refine ⟨48630756818777476656395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32420504545851651104263 48630756818777476656395)
        ·
          refine ⟨72946135228166214984593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48630756818777476656395 72946135228166214984593)
          ·
            refine ⟨54709601421124661238445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72946135228166214984593 54709601421124661238445)
            ·
              refine ⟨20516100532921747964417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54709601421124661238445 20516100532921747964417)
              ·
                refine ⟨15387075399691310973313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20516100532921747964417 15387075399691310973313)
                ·
                  refine ⟨11540306549768483229985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15387075399691310973313 11540306549768483229985)
                  ·
                    refine ⟨8655229912326362422489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11540306549768483229985 8655229912326362422489)
                    ·
                      refine ⟨6491422434244771816867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8655229912326362422489 6491422434244771816867)
                      ·
                        rfl

theorem cell23_12642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_12642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12642 prefixEnd_12642 := by exact prefixLift 12642
  have htrace : WordTrace (prefixWord ++ tailWord_12642) baseStart_12642 baseEnd_12642 := by
    simpa [prefixWord, tailWord_12642, baseEnd_12642] using wordTrace_append hprefix tailTrace_12642
  have hstable : (prefixWord ++ tailWord_12642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12642).length < 2 ^ (prefixWord ++ tailWord_12642).sum := by decide
  have hdescent : baseEnd_12642 < baseStart_12642 := by decide
  rcases family_descends (prefixWord ++ tailWord_12642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12648 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 5]
def baseStart_12648 : Nat := 118140960795 + 12648 * 2 ^ 59
def prefixEnd_12648 : Nat := 4983230072969 + 3 ^ 40 * 12648 * 2
def baseEnd_12648 : Nat := 721611479796860926871

theorem tailTrace_12648 : CollatzResearch.WordTrace tailWord_12648 prefixEnd_12648 721611479796860926871 := by
  unfold tailWord_12648
  simp only [CollatzResearch.WordTrace]
  refine ⟨230655229092965475767299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 307540305457287301023065 230655229092965475767299)
  ·
    refine ⟨345982843639448213650949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230655229092965475767299 345982843639448213650949)
    ·
      refine ⟨64871783182396540059553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 345982843639448213650949 64871783182396540059553)
      ·
        refine ⟨48653837386797405044665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64871783182396540059553 48653837386797405044665)
        ·
          refine ⟨36490378040098053783499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48653837386797405044665 36490378040098053783499)
          ·
            refine ⟨54735567060147080675249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36490378040098053783499 54735567060147080675249)
            ·
              refine ⟨41051675295110310506437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54735567060147080675249 41051675295110310506437)
              ·
                refine ⟨7697189117833183219957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41051675295110310506437 7697189117833183219957)
                ·
                  refine ⟨721611479796860926871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7697189117833183219957 721611479796860926871)
                  ·
                    rfl

theorem cell23_12648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 5].length) (baseStart_12648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12648 prefixEnd_12648 := by exact prefixLift 12648
  have htrace : WordTrace (prefixWord ++ tailWord_12648) baseStart_12648 baseEnd_12648 := by
    simpa [prefixWord, tailWord_12648, baseEnd_12648] using wordTrace_append hprefix tailTrace_12648
  have hstable : (prefixWord ++ tailWord_12648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12648).length < 2 ^ (prefixWord ++ tailWord_12648).sum := by decide
  have hdescent : baseEnd_12648 < baseStart_12648 := by decide
  rcases family_descends (prefixWord ++ tailWord_12648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12661 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_12661 : Nat := 118140960795 + 12661 * 2 ^ 59
def prefixEnd_12661 : Nat := 4983230072969 + 3 ^ 40 * 12661 * 2
def baseEnd_12661 : Nat := 2167059522226732493093

theorem tailTrace_12661 : CollatzResearch.WordTrace tailWord_12661 prefixEnd_12661 2167059522226732493093 := by
  unfold tailWord_12661
  simp only [CollatzResearch.WordTrace]
  refine ⟨461784607138834171757837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 307856404759222781171891 461784607138834171757837)
  ·
    refine ⟨173169227677062814409189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 461784607138834171757837 173169227677062814409189)
    ·
      refine ⟨32469230189449277701723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173169227677062814409189 32469230189449277701723)
      ·
        refine ⟨48703845284173916552585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32469230189449277701723 48703845284173916552585)
        ·
          refine ⟨36527883963130437414439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48703845284173916552585 36527883963130437414439)
          ·
            refine ⟨54791825944695656121659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36527883963130437414439 54791825944695656121659)
            ·
              refine ⟨82187738917043484182489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54791825944695656121659 82187738917043484182489)
              ·
                refine ⟨61640804187782613136867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82187738917043484182489 61640804187782613136867)
                ·
                  refine ⟨92461206281673919705301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61640804187782613136867 92461206281673919705301)
                  ·
                    refine ⟨2167059522226732493093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 92461206281673919705301 2167059522226732493093)
                    ·
                      rfl

theorem cell23_12661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_12661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12661 prefixEnd_12661 := by exact prefixLift 12661
  have htrace : WordTrace (prefixWord ++ tailWord_12661) baseStart_12661 baseEnd_12661 := by
    simpa [prefixWord, tailWord_12661, baseEnd_12661] using wordTrace_append hprefix tailTrace_12661
  have hstable : (prefixWord ++ tailWord_12661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12661).length < 2 ^ (prefixWord ++ tailWord_12661).sum := by decide
  have hdescent : baseEnd_12661 < baseStart_12661 := by decide
  rcases family_descends (prefixWord ++ tailWord_12661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12681 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_12681 : Nat := 118140960795 + 12681 * 2 ^ 59
def prefixEnd_12681 : Nat := 4983230072969 + 3 ^ 40 * 12681 * 2
def baseEnd_12681 : Nat := 6511448179770119229187

theorem tailTrace_12681 : CollatzResearch.WordTrace tailWord_12681 prefixEnd_12681 6511448179770119229187 := by
  unfold tailWord_12681
  simp only [CollatzResearch.WordTrace]
  refine ⟨462514067066377587485897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 308342711377585058323931 462514067066377587485897)
  ·
    refine ⟨346885550299783190614423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462514067066377587485897 346885550299783190614423)
    ·
      refine ⟨520328325449674785921635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346885550299783190614423 520328325449674785921635)
      ·
        refine ⟨780492488174512178882453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520328325449674785921635 780492488174512178882453)
        ·
          refine ⟨36585585383180258385115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 780492488174512178882453 36585585383180258385115)
          ·
            refine ⟨54878378074770387577673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36585585383180258385115 54878378074770387577673)
            ·
              refine ⟨41158783556077790683255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54878378074770387577673 41158783556077790683255)
              ·
                refine ⟨61738175334116686024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41158783556077790683255 61738175334116686024883)
                ·
                  refine ⟨92607263001175029037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61738175334116686024883 92607263001175029037325)
                  ·
                    refine ⟨34727723625440635888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92607263001175029037325 34727723625440635888997)
                    ·
                      refine ⟨6511448179770119229187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 34727723625440635888997 6511448179770119229187)
                      ·
                        rfl

theorem cell23_12681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_12681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12681 prefixEnd_12681 := by exact prefixLift 12681
  have htrace : WordTrace (prefixWord ++ tailWord_12681) baseStart_12681 baseEnd_12681 := by
    simpa [prefixWord, tailWord_12681, baseEnd_12681] using wordTrace_append hprefix tailTrace_12681
  have hstable : (prefixWord ++ tailWord_12681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12681).length < 2 ^ (prefixWord ++ tailWord_12681).sum := by decide
  have hdescent : baseEnd_12681 < baseStart_12681 := by decide
  rcases family_descends (prefixWord ++ tailWord_12681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12682 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_12682 : Nat := 118140960795 + 12682 * 2 ^ 59
def prefixEnd_12682 : Nat := 4983230072969 + 3 ^ 40 * 12682 * 2
def baseEnd_12682 : Nat := 723551295602735035187

theorem tailTrace_12682 : CollatzResearch.WordTrace tailWord_12682 prefixEnd_12682 723551295602735035187 := by
  unfold tailWord_12682
  simp only [CollatzResearch.WordTrace]
  refine ⟨115637635015688689568075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 308367026708503172181533 115637635015688689568075)
  ·
    refine ⟨173456452523533034352113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115637635015688689568075 173456452523533034352113)
    ·
      refine ⟨130092339392649775764085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173456452523533034352113 130092339392649775764085)
      ·
        refine ⟨12196156818060916477883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130092339392649775764085 12196156818060916477883)
        ·
          refine ⟨18294235227091374716825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196156818060916477883 18294235227091374716825)
          ·
            refine ⟨13720676420318531037619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18294235227091374716825 13720676420318531037619)
            ·
              refine ⟨20581014630477796556429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13720676420318531037619 20581014630477796556429)
              ·
                refine ⟨7717880486429173708661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20581014630477796556429 7717880486429173708661)
                ·
                  refine ⟨723551295602735035187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7717880486429173708661 723551295602735035187)
                  ·
                    rfl

theorem cell23_12682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_12682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12682 prefixEnd_12682 := by exact prefixLift 12682
  have htrace : WordTrace (prefixWord ++ tailWord_12682) baseStart_12682 baseEnd_12682 := by
    simpa [prefixWord, tailWord_12682, baseEnd_12682] using wordTrace_append hprefix tailTrace_12682
  have hstable : (prefixWord ++ tailWord_12682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12682).length < 2 ^ (prefixWord ++ tailWord_12682).sum := by decide
  have hdescent : baseEnd_12682 < baseStart_12682 := by decide
  rcases family_descends (prefixWord ++ tailWord_12682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12698 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_12698 : Nat := 118140960795 + 12698 * 2 ^ 59
def prefixEnd_12698 : Nat := 4983230072969 + 3 ^ 40 * 12698 * 2
def baseEnd_12698 : Nat := 6520177350896552716609

theorem tailTrace_12698 : CollatzResearch.WordTrace tailWord_12698 prefixEnd_12698 6520177350896552716609 := by
  unfold tailWord_12698
  simp only [CollatzResearch.WordTrace]
  refine ⟨115783527001197372713687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 308756072003192993903165 115783527001197372713687)
  ·
    refine ⟨173675290501796059070531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115783527001197372713687 173675290501796059070531)
    ·
      refine ⟨260512935752694088605797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173675290501796059070531 260512935752694088605797)
      ·
        refine ⟨48846175453630141613587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260512935752694088605797 48846175453630141613587)
        ·
          refine ⟨73269263180445212420381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48846175453630141613587 73269263180445212420381)
          ·
            refine ⟨27475973692666954657643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73269263180445212420381 27475973692666954657643)
            ·
              refine ⟨41213960539000431986465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27475973692666954657643 41213960539000431986465)
              ·
                refine ⟨30910470404250323989849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41213960539000431986465 30910470404250323989849)
                ·
                  refine ⟨23182852803187742992387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30910470404250323989849 23182852803187742992387)
                  ·
                    refine ⟨34774279204781614488581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23182852803187742992387 34774279204781614488581)
                    ·
                      refine ⟨6520177350896552716609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 34774279204781614488581 6520177350896552716609)
                      ·
                        rfl

theorem cell23_12698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_12698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12698 prefixEnd_12698 := by exact prefixLift 12698
  have htrace : WordTrace (prefixWord ++ tailWord_12698) baseStart_12698 baseEnd_12698 := by
    simpa [prefixWord, tailWord_12698, baseEnd_12698] using wordTrace_append hprefix tailTrace_12698
  have hstable : (prefixWord ++ tailWord_12698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12698).length < 2 ^ (prefixWord ++ tailWord_12698).sum := by decide
  have hdescent : baseEnd_12698 < baseStart_12698 := by decide
  rcases family_descends (prefixWord ++ tailWord_12698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12708 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_12708 : Nat := 118140960795 + 12708 * 2 ^ 59
def prefixEnd_12708 : Nat := 4983230072969 + 3 ^ 40 * 12708 * 2
def baseEnd_12708 : Nat := 2175104052480504530521

theorem tailTrace_12708 : CollatzResearch.WordTrace tailWord_12708 prefixEnd_12708 2175104052480504530521 := by
  unfold tailWord_12708
  simp only [CollatzResearch.WordTrace]
  refine ⟨231749418984280599359389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 308999225312374132479185 231749418984280599359389)
  ·
    refine ⟨86906032119105224759771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231749418984280599359389 86906032119105224759771)
    ·
      refine ⟨130359048178657837139657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86906032119105224759771 130359048178657837139657)
      ·
        refine ⟨97769286133993377854743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130359048178657837139657 97769286133993377854743)
        ·
          refine ⟨146653929200990066782115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97769286133993377854743 146653929200990066782115)
          ·
            refine ⟨219980893801485100173173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146653929200990066782115 219980893801485100173173)
            ·
              refine ⟨20623208793889228141235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 219980893801485100173173 20623208793889228141235)
              ·
                refine ⟨30934813190833842211853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20623208793889228141235 30934813190833842211853)
                ·
                  refine ⟨11600554946562690829445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30934813190833842211853 11600554946562690829445)
                  ·
                    refine ⟨2175104052480504530521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11600554946562690829445 2175104052480504530521)
                    ·
                      rfl

theorem cell23_12708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_12708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12708 prefixEnd_12708 := by exact prefixLift 12708
  have htrace : WordTrace (prefixWord ++ tailWord_12708) baseStart_12708 baseEnd_12708 := by
    simpa [prefixWord, tailWord_12708, baseEnd_12708] using wordTrace_append hprefix tailTrace_12708
  have hstable : (prefixWord ++ tailWord_12708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12708).length < 2 ^ (prefixWord ++ tailWord_12708).sum := by decide
  have hdescent : baseEnd_12708 < baseStart_12708 := by decide
  rcases family_descends (prefixWord ++ tailWord_12708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12758 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_12758 : Nat := 118140960795 + 12758 * 2 ^ 59
def prefixEnd_12758 : Nat := 4983230072969 + 3 ^ 40 * 12758 * 2
def baseEnd_12758 : Nat := 6550986190166317966333

theorem tailTrace_12758 : CollatzResearch.WordTrace tailWord_12758 prefixEnd_12758 6550986190166317966333 := by
  unfold tailWord_12758
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082655486713733627433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 310214991858279825359285 29082655486713733627433)
  ·
    refine ⟨21811991615035300220575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29082655486713733627433 21811991615035300220575)
    ·
      refine ⟨32717987422552950330863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21811991615035300220575 32717987422552950330863)
      ·
        refine ⟨49076981133829425496295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32717987422552950330863 49076981133829425496295)
        ·
          refine ⟨73615471700744138244443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49076981133829425496295 73615471700744138244443)
          ·
            refine ⟨110423207551116207366665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73615471700744138244443 110423207551116207366665)
            ·
              refine ⟨82817405663337155524999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110423207551116207366665 82817405663337155524999)
              ·
                refine ⟨124226108495005733287499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82817405663337155524999 124226108495005733287499)
                ·
                  refine ⟨186339162742508599931249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124226108495005733287499 186339162742508599931249)
                  ·
                    refine ⟨139754372056881449948437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186339162742508599931249 139754372056881449948437)
                    ·
                      refine ⟨6550986190166317966333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 139754372056881449948437 6550986190166317966333)
                      ·
                        rfl

theorem cell23_12758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_12758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12758 prefixEnd_12758 := by exact prefixLift 12758
  have htrace : WordTrace (prefixWord ++ tailWord_12758) baseStart_12758 baseEnd_12758 := by
    simpa [prefixWord, tailWord_12758, baseEnd_12758] using wordTrace_append hprefix tailTrace_12758
  have hstable : (prefixWord ++ tailWord_12758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12758).length < 2 ^ (prefixWord ++ tailWord_12758).sum := by decide
  have hdescent : baseEnd_12758 < baseStart_12758 := by decide
  rcases family_descends (prefixWord ++ tailWord_12758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12765 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_12765 : Nat := 118140960795 + 12765 * 2 ^ 59
def prefixEnd_12765 : Nat := 4983230072969 + 3 ^ 40 * 12765 * 2
def baseEnd_12765 : Nat := 6554580554747790578801

theorem tailTrace_12765 : CollatzResearch.WordTrace tailWord_12765 prefixEnd_12765 6554580554747790578801 := by
  unfold tailWord_12765
  simp only [CollatzResearch.WordTrace]
  refine ⟨465577798762059933543749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 310385199174706622362499 465577798762059933543749)
  ·
    refine ⟨87295837267886237539453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 465577798762059933543749 87295837267886237539453)
    ·
      refine ⟨32735938975457339077295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87295837267886237539453 32735938975457339077295)
      ·
        refine ⟨49103908463186008615943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32735938975457339077295 49103908463186008615943)
        ·
          refine ⟨73655862694779012923915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49103908463186008615943 73655862694779012923915)
          ·
            refine ⟨110483794042168519385873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73655862694779012923915 110483794042168519385873)
            ·
              refine ⟨82862845531626389539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110483794042168519385873 82862845531626389539405)
              ·
                refine ⟨31073567074359896077277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82862845531626389539405 31073567074359896077277)
                ·
                  refine ⟨11652587652884961028979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31073567074359896077277 11652587652884961028979)
                  ·
                    refine ⟨17478881479327441543469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11652587652884961028979 17478881479327441543469)
                    ·
                      refine ⟨6554580554747790578801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 17478881479327441543469 6554580554747790578801)
                      ·
                        rfl

theorem cell23_12765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_12765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12765 prefixEnd_12765 := by exact prefixLift 12765
  have htrace : WordTrace (prefixWord ++ tailWord_12765) baseStart_12765 baseEnd_12765 := by
    simpa [prefixWord, tailWord_12765, baseEnd_12765] using wordTrace_append hprefix tailTrace_12765
  have hstable : (prefixWord ++ tailWord_12765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12765).length < 2 ^ (prefixWord ++ tailWord_12765).sum := by decide
  have hdescent : baseEnd_12765 < baseStart_12765 := by decide
  rcases family_descends (prefixWord ++ tailWord_12765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12802 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_12802 : Nat := 118140960795 + 12802 * 2 ^ 59
def prefixEnd_12802 : Nat := 4983230072969 + 3 ^ 40 * 12802 * 2
def baseEnd_12802 : Nat := 2191193112988048605377

theorem tailTrace_12802 : CollatzResearch.WordTrace tailWord_12802 prefixEnd_12802 2191193112988048605377 := by
  unfold tailWord_12802
  simp only [CollatzResearch.WordTrace]
  refine ⟨116731824907003813160165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 311284866418676835093773 116731824907003813160165)
  ·
    refine ⟨21887217170063214967531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116731824907003813160165 21887217170063214967531)
    ·
      refine ⟨32830825755094822451297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21887217170063214967531 32830825755094822451297)
      ·
        refine ⟨24623119316321116838473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32830825755094822451297 24623119316321116838473)
        ·
          refine ⟨18467339487240837628855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24623119316321116838473 18467339487240837628855)
          ·
            refine ⟨27701009230861256443283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18467339487240837628855 27701009230861256443283)
            ·
              refine ⟨41551513846291884664925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27701009230861256443283 41551513846291884664925)
              ·
                refine ⟨15581817692359456749347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41551513846291884664925 15581817692359456749347)
                ·
                  refine ⟨23372726538539185124021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15581817692359456749347 23372726538539185124021)
                  ·
                    refine ⟨2191193112988048605377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23372726538539185124021 2191193112988048605377)
                    ·
                      rfl

theorem cell23_12802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_12802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12802 prefixEnd_12802 := by exact prefixLift 12802
  have htrace : WordTrace (prefixWord ++ tailWord_12802) baseStart_12802 baseEnd_12802 := by
    simpa [prefixWord, tailWord_12802, baseEnd_12802] using wordTrace_append hprefix tailTrace_12802
  have hstable : (prefixWord ++ tailWord_12802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12802).length < 2 ^ (prefixWord ++ tailWord_12802).sum := by decide
  have hdescent : baseEnd_12802 < baseStart_12802 := by decide
  rcases family_descends (prefixWord ++ tailWord_12802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12805 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_12805 : Nat := 118140960795 + 12805 * 2 ^ 59
def prefixEnd_12805 : Nat := 4983230072969 + 3 ^ 40 * 12805 * 2
def baseEnd_12805 : Nat := 6575119780927634078617

theorem tailTrace_12805 : CollatzResearch.WordTrace tailWord_12805 prefixEnd_12805 6575119780927634078617 := by
  unfold tailWord_12805
  simp only [CollatzResearch.WordTrace]
  refine ⟨467036718617146764999869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311357812411431176666579 467036718617146764999869)
  ·
    refine ⟨175138769481430036874951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 467036718617146764999869 175138769481430036874951)
    ·
      refine ⟨262708154222145055312427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175138769481430036874951 262708154222145055312427)
      ·
        refine ⟨394062231333217582968641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262708154222145055312427 394062231333217582968641)
        ·
          refine ⟨295546673499913187226481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394062231333217582968641 295546673499913187226481)
          ·
            refine ⟨221660005124934890419861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295546673499913187226481 221660005124934890419861)
            ·
              refine ⟨10390312740231322988431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 221660005124934890419861 10390312740231322988431)
              ·
                refine ⟨15585469110346984482647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10390312740231322988431 15585469110346984482647)
                ·
                  refine ⟨23378203665520476723971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15585469110346984482647 23378203665520476723971)
                  ·
                    refine ⟨35067305498280715085957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23378203665520476723971 35067305498280715085957)
                    ·
                      refine ⟨6575119780927634078617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 35067305498280715085957 6575119780927634078617)
                      ·
                        rfl

theorem cell23_12805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_12805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12805 prefixEnd_12805 := by exact prefixLift 12805
  have htrace : WordTrace (prefixWord ++ tailWord_12805) baseStart_12805 baseEnd_12805 := by
    simpa [prefixWord, tailWord_12805, baseEnd_12805] using wordTrace_append hprefix tailTrace_12805
  have hstable : (prefixWord ++ tailWord_12805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12805).length < 2 ^ (prefixWord ++ tailWord_12805).sum := by decide
  have hdescent : baseEnd_12805 < baseStart_12805 := by decide
  rcases family_descends (prefixWord ++ tailWord_12805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12811 : List Nat := [1, 1, 1, 1, 7, 2, 10]
def baseStart_12811 : Nat := 118140960795 + 12811 * 2 ^ 59
def prefixEnd_12811 : Nat := 4983230072969 + 3 ^ 40 * 12811 * 2
def baseEnd_12811 : Nat := 81212353887093958069

theorem tailTrace_12811 : CollatzResearch.WordTrace tailWord_12811 prefixEnd_12811 81212353887093958069 := by
  unfold tailWord_12811
  simp only [CollatzResearch.WordTrace]
  refine ⟨467255556595409789718287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311503704396939859812191 467255556595409789718287)
  ·
    refine ⟨700883334893114684577431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467255556595409789718287 700883334893114684577431)
    ·
      refine ⟨1051325002339672026866147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700883334893114684577431 1051325002339672026866147)
      ·
        refine ⟨1576987503509508040299221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1051325002339672026866147 1576987503509508040299221)
        ·
          refine ⟨36960644613504094694513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1576987503509508040299221 36960644613504094694513)
          ·
            refine ⟨27720483460128071020885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36960644613504094694513 27720483460128071020885)
            ·
              refine ⟨81212353887093958069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 27720483460128071020885 81212353887093958069)
              ·
                rfl

theorem cell23_12811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 10].length) (baseStart_12811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12811 prefixEnd_12811 := by exact prefixLift 12811
  have htrace : WordTrace (prefixWord ++ tailWord_12811) baseStart_12811 baseEnd_12811 := by
    simpa [prefixWord, tailWord_12811, baseEnd_12811] using wordTrace_append hprefix tailTrace_12811
  have hstable : (prefixWord ++ tailWord_12811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12811).length < 2 ^ (prefixWord ++ tailWord_12811).sum := by decide
  have hdescent : baseEnd_12811 < baseStart_12811 := by decide
  rcases family_descends (prefixWord ++ tailWord_12811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12832 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_12832 : Nat := 118140960795 + 12832 * 2 ^ 59
def prefixEnd_12832 : Nat := 4983230072969 + 3 ^ 40 * 12832 * 2
def baseEnd_12832 : Nat := 2196327919533009480331

theorem tailTrace_12832 : CollatzResearch.WordTrace tailWord_12832 prefixEnd_12832 2196327919533009480331 := by
  unfold tailWord_12832
  simp only [CollatzResearch.WordTrace]
  refine ⟨234010744759665188116375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 312014326346220250821833 234010744759665188116375)
  ·
    refine ⟨351016117139497782174563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234010744759665188116375 351016117139497782174563)
    ·
      refine ⟨526524175709246673261845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351016117139497782174563 526524175709246673261845)
      ·
        refine ⟨24680820736370937809149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 526524175709246673261845 24680820736370937809149)
        ·
          refine ⟨9255307776139101678431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24680820736370937809149 9255307776139101678431)
          ·
            refine ⟨13882961664208652517647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9255307776139101678431 13882961664208652517647)
            ·
              refine ⟨20824442496312978776471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882961664208652517647 20824442496312978776471)
              ·
                refine ⟨31236663744469468164707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20824442496312978776471 31236663744469468164707)
                ·
                  refine ⟨46854995616704202247061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31236663744469468164707 46854995616704202247061)
                  ·
                    refine ⟨2196327919533009480331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46854995616704202247061 2196327919533009480331)
                    ·
                      rfl

theorem cell23_12832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_12832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12832 prefixEnd_12832 := by exact prefixLift 12832
  have htrace : WordTrace (prefixWord ++ tailWord_12832) baseStart_12832 baseEnd_12832 := by
    simpa [prefixWord, tailWord_12832, baseEnd_12832] using wordTrace_append hprefix tailTrace_12832
  have hstable : (prefixWord ++ tailWord_12832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12832).length < 2 ^ (prefixWord ++ tailWord_12832).sum := by decide
  have hdescent : baseEnd_12832 < baseStart_12832 := by decide
  rcases family_descends (prefixWord ++ tailWord_12832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12835 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 4]
def baseStart_12835 : Nat := 118140960795 + 12835 * 2 ^ 59
def prefixEnd_12835 : Nat := 4983230072969 + 3 ^ 40 * 12835 * 2
def baseEnd_12835 : Nat := 6590524200562516703479

theorem tailTrace_12835 : CollatzResearch.WordTrace tailWord_12835 prefixEnd_12835 6590524200562516703479 := by
  unfold tailWord_12835
  simp only [CollatzResearch.WordTrace]
  refine ⟨468130908508461888591959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312087272338974592394639 468130908508461888591959)
  ·
    refine ⟨702196362762692832887939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468130908508461888591959 702196362762692832887939)
    ·
      refine ⟨1053294544144039249331909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702196362762692832887939 1053294544144039249331909)
      ·
        refine ⟨197492727027007359249733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1053294544144039249331909 197492727027007359249733)
        ·
          refine ⟨37029886317563879859325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197492727027007359249733 37029886317563879859325)
          ·
            refine ⟨13886207369086454947247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37029886317563879859325 13886207369086454947247)
            ·
              refine ⟨20829311053629682420871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886207369086454947247 20829311053629682420871)
              ·
                refine ⟨31243966580444523631307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20829311053629682420871 31243966580444523631307)
                ·
                  refine ⟨46865949870666785446961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31243966580444523631307 46865949870666785446961)
                  ·
                    refine ⟨35149462403000089085221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46865949870666785446961 35149462403000089085221)
                    ·
                      refine ⟨6590524200562516703479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 35149462403000089085221 6590524200562516703479)
                      ·
                        rfl

theorem cell23_12835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_12835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12835 prefixEnd_12835 := by exact prefixLift 12835
  have htrace : WordTrace (prefixWord ++ tailWord_12835) baseStart_12835 baseEnd_12835 := by
    simpa [prefixWord, tailWord_12835, baseEnd_12835] using wordTrace_append hprefix tailTrace_12835
  have hstable : (prefixWord ++ tailWord_12835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12835).length < 2 ^ (prefixWord ++ tailWord_12835).sum := by decide
  have hdescent : baseEnd_12835 < baseStart_12835 := by decide
  rcases family_descends (prefixWord ++ tailWord_12835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12839 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_12839 : Nat := 118140960795 + 12839 * 2 ^ 59
def prefixEnd_12839 : Nat := 4983230072969 + 3 ^ 40 * 12839 * 2
def baseEnd_12839 : Nat := 6592578123180501053461

theorem tailTrace_12839 : CollatzResearch.WordTrace tailWord_12839 prefixEnd_12839 6592578123180501053461 := by
  unfold tailWord_12839
  simp only [CollatzResearch.WordTrace]
  refine ⟨468276800493970571737571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312184533662647047825047 468276800493970571737571)
  ·
    refine ⟨702415200740955857606357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468276800493970571737571 702415200740955857606357)
    ·
      refine ⟨16462856267366152912649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 702415200740955857606357 16462856267366152912649)
      ·
        refine ⟨12347142200524614684487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16462856267366152912649 12347142200524614684487)
        ·
          refine ⟨18520713300786922026731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347142200524614684487 18520713300786922026731)
          ·
            refine ⟨27781069951180383040097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18520713300786922026731 27781069951180383040097)
            ·
              refine ⟨20835802463385287280073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27781069951180383040097 20835802463385287280073)
              ·
                refine ⟨15626851847538965460055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20835802463385287280073 15626851847538965460055)
                ·
                  refine ⟨23440277771308448190083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15626851847538965460055 23440277771308448190083)
                  ·
                    refine ⟨35160416656962672285125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23440277771308448190083 35160416656962672285125)
                    ·
                      refine ⟨6592578123180501053461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 35160416656962672285125 6592578123180501053461)
                      ·
                        rfl

theorem cell23_12839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_12839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12839 prefixEnd_12839 := by exact prefixLift 12839
  have htrace : WordTrace (prefixWord ++ tailWord_12839) baseStart_12839 baseEnd_12839 := by
    simpa [prefixWord, tailWord_12839, baseEnd_12839] using wordTrace_append hprefix tailTrace_12839
  have hstable : (prefixWord ++ tailWord_12839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12839).length < 2 ^ (prefixWord ++ tailWord_12839).sum := by decide
  have hdescent : baseEnd_12839 < baseStart_12839 := by decide
  rcases family_descends (prefixWord ++ tailWord_12839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12842 : List Nat := [3, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_12842 : Nat := 118140960795 + 12842 * 2 ^ 59
def prefixEnd_12842 : Nat := 4983230072969 + 3 ^ 40 * 12842 * 2
def baseEnd_12842 : Nat := 6594118565143989315947

theorem tailTrace_12842 : CollatzResearch.WordTrace tailWord_12842 prefixEnd_12842 6594118565143989315947 := by
  unfold tailWord_12842
  simp only [CollatzResearch.WordTrace]
  refine ⟨117096554870775521024195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 312257479655401389397853 117096554870775521024195)
  ·
    refine ⟨175644832306163281536293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117096554870775521024195 175644832306163281536293)
    ·
      refine ⟨32933406057405615288055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175644832306163281536293 32933406057405615288055)
      ·
        refine ⟨49400109086108422932083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32933406057405615288055 49400109086108422932083)
        ·
          refine ⟨74100163629162634398125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49400109086108422932083 74100163629162634398125)
          ·
            refine ⟨27787561360935987899297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74100163629162634398125 27787561360935987899297)
            ·
              refine ⟨20840671020701990924473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27787561360935987899297 20840671020701990924473)
              ·
                refine ⟨15630503265526493193355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20840671020701990924473 15630503265526493193355)
                ·
                  refine ⟨23445754898289739790033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15630503265526493193355 23445754898289739790033)
                  ·
                    refine ⟨17584316173717304842525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23445754898289739790033 17584316173717304842525)
                    ·
                      refine ⟨6594118565143989315947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 17584316173717304842525 6594118565143989315947)
                      ·
                        rfl

theorem cell23_12842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_12842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12842 prefixEnd_12842 := by exact prefixLift 12842
  have htrace : WordTrace (prefixWord ++ tailWord_12842) baseStart_12842 baseEnd_12842 := by
    simpa [prefixWord, tailWord_12842, baseEnd_12842] using wordTrace_append hprefix tailTrace_12842
  have hstable : (prefixWord ++ tailWord_12842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12842).length < 2 ^ (prefixWord ++ tailWord_12842).sum := by decide
  have hdescent : baseEnd_12842 < baseStart_12842 := by decide
  rcases family_descends (prefixWord ++ tailWord_12842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12851 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_12851 : Nat := 118140960795 + 12851 * 2 ^ 59
def prefixEnd_12851 : Nat := 4983230072969 + 3 ^ 40 * 12851 * 2
def baseEnd_12851 : Nat := 6598739891034454103405

theorem tailTrace_12851 : CollatzResearch.WordTrace tailWord_12851 prefixEnd_12851 6598739891034454103405 := by
  unfold tailWord_12851
  simp only [CollatzResearch.WordTrace]
  refine ⟨468714476450496621174407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312476317633664414116271 468714476450496621174407)
  ·
    refine ⟨703071714675744931761611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 468714476450496621174407 703071714675744931761611)
    ·
      refine ⟨1054607572013617397642417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703071714675744931761611 1054607572013617397642417)
      ·
        refine ⟨790955679010213048231813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054607572013617397642417 790955679010213048231813)
        ·
          refine ⟨148304189814414946543465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 790955679010213048231813 148304189814414946543465)
          ·
            refine ⟨111228142360811209907599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148304189814414946543465 111228142360811209907599)
            ·
              refine ⟨166842213541216814861399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111228142360811209907599 166842213541216814861399)
              ·
                refine ⟨250263320311825222292099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166842213541216814861399 250263320311825222292099)
                ·
                  refine ⟨375394980467737833438149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250263320311825222292099 375394980467737833438149)
                  ·
                    refine ⟨70386558837700843769653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375394980467737833438149 70386558837700843769653)
                    ·
                      refine ⟨6598739891034454103405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 70386558837700843769653 6598739891034454103405)
                      ·
                        rfl

theorem cell23_12851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_12851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12851 prefixEnd_12851 := by exact prefixLift 12851
  have htrace : WordTrace (prefixWord ++ tailWord_12851) baseStart_12851 baseEnd_12851 := by
    simpa [prefixWord, tailWord_12851, baseEnd_12851] using wordTrace_append hprefix tailTrace_12851
  have hstable : (prefixWord ++ tailWord_12851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12851).length < 2 ^ (prefixWord ++ tailWord_12851).sum := by decide
  have hdescent : baseEnd_12851 < baseStart_12851 := by decide
  rcases family_descends (prefixWord ++ tailWord_12851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12862 : List Nat := [4, 2, 1, 4, 2, 1, 9]
def baseStart_12862 : Nat := 118140960795 + 12862 * 2 ^ 59
def prefixEnd_12862 : Nat := 4983230072969 + 3 ^ 40 * 12862 * 2
def baseEnd_12862 : Nat := 81535656521406309455

theorem tailTrace_12862 : CollatzResearch.WordTrace tailWord_12862 prefixEnd_12862 81535656521406309455 := by
  unfold tailWord_12862
  simp only [CollatzResearch.WordTrace]
  refine ⟨58639459926330687478105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 312743786273763666549893 58639459926330687478105)
  ·
    refine ⟨43979594944748015608579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58639459926330687478105 43979594944748015608579)
    ·
      refine ⟨65969392417122023412869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43979594944748015608579 65969392417122023412869)
      ·
        refine ⟨12369261078210379389913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65969392417122023412869 12369261078210379389913)
        ·
          refine ⟨9276945808657784542435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12369261078210379389913 9276945808657784542435)
          ·
            refine ⟨13915418712986676813653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9276945808657784542435 13915418712986676813653)
            ·
              refine ⟨81535656521406309455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 13915418712986676813653 81535656521406309455)
              ·
                rfl

theorem cell23_12862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 9].length) (baseStart_12862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12862 prefixEnd_12862 := by exact prefixLift 12862
  have htrace : WordTrace (prefixWord ++ tailWord_12862) baseStart_12862 baseEnd_12862 := by
    simpa [prefixWord, tailWord_12862, baseEnd_12862] using wordTrace_append hprefix tailTrace_12862
  have hstable : (prefixWord ++ tailWord_12862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12862).length < 2 ^ (prefixWord ++ tailWord_12862).sum := by decide
  have hdescent : baseEnd_12862 < baseStart_12862 := by decide
  rcases family_descends (prefixWord ++ tailWord_12862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12912 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2]
def baseStart_12912 : Nat := 118140960795 + 12912 * 2 ^ 59
def prefixEnd_12912 : Nat := 4983230072969 + 3 ^ 40 * 12912 * 2
def baseEnd_12912 : Nat := 6630062210958715440625

theorem tailTrace_12912 : CollatzResearch.WordTrace tailWord_12912 prefixEnd_12912 6630062210958715440625 := by
  unfold tailWord_12912
  simp only [CollatzResearch.WordTrace]
  refine ⟨235469664614752019572495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 313959552819669359429993 235469664614752019572495)
  ·
    refine ⟨353204496922128029358743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235469664614752019572495 353204496922128029358743)
    ·
      refine ⟨529806745383192044038115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353204496922128029358743 529806745383192044038115)
      ·
        refine ⟨794710118074788066057173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529806745383192044038115 794710118074788066057173)
        ·
          refine ⟨18626018392377845298215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 794710118074788066057173 18626018392377845298215)
          ·
            refine ⟨27939027588566767947323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626018392377845298215 27939027588566767947323)
            ·
              refine ⟨41908541382850151920985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27939027588566767947323 41908541382850151920985)
              ·
                refine ⟨31431406037137613940739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41908541382850151920985 31431406037137613940739)
                ·
                  refine ⟨47147109055706420911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31431406037137613940739 47147109055706420911109)
                  ·
                    refine ⟨8840082947944953920833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47147109055706420911109 8840082947944953920833)
                    ·
                      refine ⟨6630062210958715440625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8840082947944953920833 6630062210958715440625)
                      ·
                        rfl

theorem cell23_12912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2].length) (baseStart_12912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12912 prefixEnd_12912 := by exact prefixLift 12912
  have htrace : WordTrace (prefixWord ++ tailWord_12912) baseStart_12912 baseEnd_12912 := by
    simpa [prefixWord, tailWord_12912, baseEnd_12912] using wordTrace_append hprefix tailTrace_12912
  have hstable : (prefixWord ++ tailWord_12912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12912).length < 2 ^ (prefixWord ++ tailWord_12912).sum := by decide
  have hdescent : baseEnd_12912 < baseStart_12912 := by decide
  rcases family_descends (prefixWord ++ tailWord_12912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12929 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_12929 : Nat := 118140960795 + 12929 * 2 ^ 59
def prefixEnd_12929 : Nat := 4983230072969 + 3 ^ 40 * 12929 * 2
def baseEnd_12929 : Nat := 6638791382085148928047

theorem tailTrace_12929 : CollatzResearch.WordTrace tailWord_12929 prefixEnd_12929 6638791382085148928047 := by
  unfold tailWord_12929
  simp only [CollatzResearch.WordTrace]
  refine ⟨471559370167915942513841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 314372913445277295009227 471559370167915942513841)
  ·
    refine ⟨353669527625936956885381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 471559370167915942513841 353669527625936956885381)
    ·
      refine ⟨66313036429863179416009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353669527625936956885381 66313036429863179416009)
      ·
        refine ⟨49734777322397384562007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66313036429863179416009 49734777322397384562007)
        ·
          refine ⟨74602165983596076843011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49734777322397384562007 74602165983596076843011)
          ·
            refine ⟨111903248975394115264517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74602165983596076843011 111903248975394115264517)
            ·
              refine ⟨20981859182886396612097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111903248975394115264517 20981859182886396612097)
              ·
                refine ⟨15736394387164797459073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20981859182886396612097 15736394387164797459073)
                ·
                  refine ⟨11802295790373598094305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15736394387164797459073 11802295790373598094305)
                  ·
                    refine ⟨8851721842780198570729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11802295790373598094305 8851721842780198570729)
                    ·
                      refine ⟨6638791382085148928047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8851721842780198570729 6638791382085148928047)
                      ·
                        rfl

theorem cell23_12929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_12929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12929 prefixEnd_12929 := by exact prefixLift 12929
  have htrace : WordTrace (prefixWord ++ tailWord_12929) baseStart_12929 baseEnd_12929 := by
    simpa [prefixWord, tailWord_12929, baseEnd_12929] using wordTrace_append hprefix tailTrace_12929
  have hstable : (prefixWord ++ tailWord_12929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12929).length < 2 ^ (prefixWord ++ tailWord_12929).sum := by decide
  have hdescent : baseEnd_12929 < baseStart_12929 := by decide
  rcases family_descends (prefixWord ++ tailWord_12929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12935 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 5]
def baseStart_12935 : Nat := 118140960795 + 12935 * 2 ^ 59
def prefixEnd_12935 : Nat := 4983230072969 + 3 ^ 40 * 12935 * 2
def baseEnd_12935 : Nat := 737985807334680605891

theorem tailTrace_12935 : CollatzResearch.WordTrace tailWord_12935 prefixEnd_12935 737985807334680605891 := by
  unfold tailWord_12935
  simp only [CollatzResearch.WordTrace]
  refine ⟨471778208146178967232259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 314518805430785978154839 471778208146178967232259)
  ·
    refine ⟨707667312219268450848389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471778208146178967232259 707667312219268450848389)
    ·
      refine ⟨132687621041112834534073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 707667312219268450848389 132687621041112834534073)
      ·
        refine ⟨99515715780834625900555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132687621041112834534073 99515715780834625900555)
        ·
          refine ⟨149273573671251938850833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99515715780834625900555 149273573671251938850833)
          ·
            refine ⟨111955180253438954138125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149273573671251938850833 111955180253438954138125)
            ·
              refine ⟨41983192595039607801797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111955180253438954138125 41983192595039607801797)
              ·
                refine ⟨7871848611569926462837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41983192595039607801797 7871848611569926462837)
                ·
                  refine ⟨737985807334680605891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7871848611569926462837 737985807334680605891)
                  ·
                    rfl

theorem cell23_12935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 5].length) (baseStart_12935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_12935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_12935 prefixEnd_12935 := by exact prefixLift 12935
  have htrace : WordTrace (prefixWord ++ tailWord_12935) baseStart_12935 baseEnd_12935 := by
    simpa [prefixWord, tailWord_12935, baseEnd_12935] using wordTrace_append hprefix tailTrace_12935
  have hstable : (prefixWord ++ tailWord_12935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12935).length < 2 ^ (prefixWord ++ tailWord_12935).sum := by decide
  have hdescent : baseEnd_12935 < baseStart_12935 := by decide
  rcases family_descends (prefixWord ++ tailWord_12935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13002 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_13002 : Nat := 118140960795 + 13002 * 2 ^ 59
def prefixEnd_13002 : Nat := 4983230072969 + 3 ^ 40 * 13002 * 2
def baseEnd_13002 : Nat := 6676275469863363315211

theorem tailTrace_13002 : CollatzResearch.WordTrace tailWord_13002 prefixEnd_13002 6676275469863363315211 := by
  unfold tailWord_13002
  simp only [CollatzResearch.WordTrace]
  refine ⟨118555474725862352480315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 316147932602299606614173 118555474725862352480315)
  ·
    refine ⟨177833212088793528720473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118555474725862352480315 177833212088793528720473)
    ·
      refine ⟨133374909066595146540355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177833212088793528720473 133374909066595146540355)
      ·
        refine ⟨200062363599892719810533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133374909066595146540355 200062363599892719810533)
        ·
          refine ⟨37511693174979884964475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200062363599892719810533 37511693174979884964475)
          ·
            refine ⟨56267539762469827446713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37511693174979884964475 56267539762469827446713)
            ·
              refine ⟨42200654821852370585035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56267539762469827446713 42200654821852370585035)
              ·
                refine ⟨63300982232778555877553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42200654821852370585035 63300982232778555877553)
                ·
                  refine ⟨47475736674583916908165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63300982232778555877553 47475736674583916908165)
                  ·
                    refine ⟨8901700626484484420281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47475736674583916908165 8901700626484484420281)
                    ·
                      refine ⟨6676275469863363315211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8901700626484484420281 6676275469863363315211)
                      ·
                        rfl

theorem cell23_13002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_13002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13002 prefixEnd_13002 := by exact prefixLift 13002
  have htrace : WordTrace (prefixWord ++ tailWord_13002) baseStart_13002 baseEnd_13002 := by
    simpa [prefixWord, tailWord_13002, baseEnd_13002] using wordTrace_append hprefix tailTrace_13002
  have hstable : (prefixWord ++ tailWord_13002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13002).length < 2 ^ (prefixWord ++ tailWord_13002).sum := by decide
  have hdescent : baseEnd_13002 < baseStart_13002 := by decide
  rcases family_descends (prefixWord ++ tailWord_13002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13029 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_13029 : Nat := 118140960795 + 13029 * 2 ^ 59
def prefixEnd_13029 : Nat := 4983230072969 + 3 ^ 40 * 13029 * 2
def baseEnd_13029 : Nat := 2230046482511585892529

theorem tailTrace_13029 : CollatzResearch.WordTrace tailWord_13029 prefixEnd_13029 2230046482511585892529 := by
  unfold tailWord_13029
  simp only [CollatzResearch.WordTrace]
  refine ⟨475206669805633021154141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 316804446537088680769427 475206669805633021154141)
  ·
    refine ⟨178202501177112382932803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 475206669805633021154141 178202501177112382932803)
    ·
      refine ⟨267303751765668574399205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178202501177112382932803 267303751765668574399205)
      ·
        refine ⟨50119453456062857699851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267303751765668574399205 50119453456062857699851)
        ·
          refine ⟨75179180184094286549777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50119453456062857699851 75179180184094286549777)
          ·
            refine ⟨56384385138070714912333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75179180184094286549777 56384385138070714912333)
            ·
              refine ⟨21144144426776518092125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56384385138070714912333 21144144426776518092125)
              ·
                refine ⟨7929054160041194284547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21144144426776518092125 7929054160041194284547)
                ·
                  refine ⟨11893581240061791426821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7929054160041194284547 11893581240061791426821)
                  ·
                    refine ⟨2230046482511585892529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11893581240061791426821 2230046482511585892529)
                    ·
                      rfl

theorem cell23_13029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_13029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13029 prefixEnd_13029 := by exact prefixLift 13029
  have htrace : WordTrace (prefixWord ++ tailWord_13029) baseStart_13029 baseEnd_13029 := by
    simpa [prefixWord, tailWord_13029, baseEnd_13029] using wordTrace_append hprefix tailTrace_13029
  have hstable : (prefixWord ++ tailWord_13029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13029).length < 2 ^ (prefixWord ++ tailWord_13029).sum := by decide
  have hdescent : baseEnd_13029 < baseStart_13029 := by decide
  rcases family_descends (prefixWord ++ tailWord_13029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13046 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_13046 : Nat := 118140960795 + 13046 * 2 ^ 59
def prefixEnd_13046 : Nat := 4983230072969 + 3 ^ 40 * 13046 * 2
def baseEnd_13046 : Nat := 2232956206220397055003

theorem tailTrace_13046 : CollatzResearch.WordTrace tailWord_13046 prefixEnd_13046 2232956206220397055003 := by
  unfold tailWord_13046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29739169421502807782687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 317217807162696616348661 29739169421502807782687)
  ·
    refine ⟨44608754132254211674031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29739169421502807782687 44608754132254211674031)
    ·
      refine ⟨66913131198381317511047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44608754132254211674031 66913131198381317511047)
      ·
        refine ⟨100369696797571976266571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66913131198381317511047 100369696797571976266571)
        ·
          refine ⟨150554545196357964399857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100369696797571976266571 150554545196357964399857)
          ·
            refine ⟨112915908897268473299893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150554545196357964399857 112915908897268473299893)
            ·
              refine ⟨10585866459118919371865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112915908897268473299893 10585866459118919371865)
              ·
                refine ⟨7939399844339189528899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10585866459118919371865 7939399844339189528899)
                ·
                  refine ⟨11909099766508784293349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7939399844339189528899 11909099766508784293349)
                  ·
                    refine ⟨2232956206220397055003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11909099766508784293349 2232956206220397055003)
                    ·
                      rfl

theorem cell23_13046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_13046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13046 prefixEnd_13046 := by exact prefixLift 13046
  have htrace : WordTrace (prefixWord ++ tailWord_13046) baseStart_13046 baseEnd_13046 := by
    simpa [prefixWord, tailWord_13046, baseEnd_13046] using wordTrace_append hprefix tailTrace_13046
  have hstable : (prefixWord ++ tailWord_13046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13046).length < 2 ^ (prefixWord ++ tailWord_13046).sum := by decide
  have hdescent : baseEnd_13046 < baseStart_13046 := by decide
  rcases family_descends (prefixWord ++ tailWord_13046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13075 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4]
def baseStart_13075 : Nat := 118140960795 + 13075 * 2 ^ 59
def prefixEnd_13075 : Nat := 4983230072969 + 3 ^ 40 * 13075 * 2
def baseEnd_13075 : Nat := 6713759557641577702375

theorem tailTrace_13075 : CollatzResearch.WordTrace tailWord_13075 prefixEnd_13075 6713759557641577702375 := by
  unfold tailWord_13075
  simp only [CollatzResearch.WordTrace]
  refine ⟨476884427638982877328679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 317922951759321918219119 476884427638982877328679)
  ·
    refine ⟨715326641458474315993019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 476884427638982877328679 715326641458474315993019)
    ·
      refine ⟨1072989962187711473989529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715326641458474315993019 1072989962187711473989529)
      ·
        refine ⟨804742471640783605492147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072989962187711473989529 804742471640783605492147)
        ·
          refine ⟨1207113707461175408238221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804742471640783605492147 1207113707461175408238221)
          ·
            refine ⟨452667640297940778089333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1207113707461175408238221 452667640297940778089333)
            ·
              refine ⟨42437591277931947945875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 452667640297940778089333 42437591277931947945875)
              ·
                refine ⟨63656386916897921918813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42437591277931947945875 63656386916897921918813)
                ·
                  refine ⟨23871145093836720719555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63656386916897921918813 23871145093836720719555)
                  ·
                    refine ⟨35806717640755081079333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23871145093836720719555 35806717640755081079333)
                    ·
                      refine ⟨6713759557641577702375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 35806717640755081079333 6713759557641577702375)
                      ·
                        rfl

theorem cell23_13075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_13075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13075 prefixEnd_13075 := by exact prefixLift 13075
  have htrace : WordTrace (prefixWord ++ tailWord_13075) baseStart_13075 baseEnd_13075 := by
    simpa [prefixWord, tailWord_13075, baseEnd_13075] using wordTrace_append hprefix tailTrace_13075
  have hstable : (prefixWord ++ tailWord_13075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13075).length < 2 ^ (prefixWord ++ tailWord_13075).sum := by decide
  have hdescent : baseEnd_13075 < baseStart_13075 := by decide
  rcases family_descends (prefixWord ++ tailWord_13075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13105 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_13105 : Nat := 118140960795 + 13105 * 2 ^ 59
def prefixEnd_13105 : Nat := 4983230072969 + 3 ^ 40 * 13105 * 2
def baseEnd_13105 : Nat := 6729163977276460327237

theorem tailTrace_13105 : CollatzResearch.WordTrace tailWord_13105 prefixEnd_13105 6729163977276460327237 := by
  unfold tailWord_13105
  simp only [CollatzResearch.WordTrace]
  refine ⟨477978617530298000920769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 318652411686865333947179 477978617530298000920769)
  ·
    refine ⟨358483963147723500690577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 477978617530298000920769 358483963147723500690577)
    ·
      refine ⟨268862972360792625517933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 358483963147723500690577 268862972360792625517933)
      ·
        refine ⟨100823614635297234569225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268862972360792625517933 100823614635297234569225)
        ·
          refine ⟨75617710976472925926919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100823614635297234569225 75617710976472925926919)
          ·
            refine ⟨113426566464709388890379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75617710976472925926919 113426566464709388890379)
            ·
              refine ⟨170139849697064083335569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113426566464709388890379 170139849697064083335569)
              ·
                refine ⟨127604887272798062501677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170139849697064083335569 127604887272798062501677)
                ·
                  refine ⟨47851832727299273438129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127604887272798062501677 47851832727299273438129)
                  ·
                    refine ⟨35888874545474455078597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47851832727299273438129 35888874545474455078597)
                    ·
                      refine ⟨6729163977276460327237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 35888874545474455078597 6729163977276460327237)
                      ·
                        rfl

theorem cell23_13105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_13105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13105 prefixEnd_13105 := by exact prefixLift 13105
  have htrace : WordTrace (prefixWord ++ tailWord_13105) baseStart_13105 baseEnd_13105 := by
    simpa [prefixWord, tailWord_13105, baseEnd_13105] using wordTrace_append hprefix tailTrace_13105
  have hstable : (prefixWord ++ tailWord_13105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13105).length < 2 ^ (prefixWord ++ tailWord_13105).sum := by decide
  have hdescent : baseEnd_13105 < baseStart_13105 := by decide
  rcases family_descends (prefixWord ++ tailWord_13105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13132 : List Nat := [2, 2, 1, 3, 3, 2, 3, 7]
def baseStart_13132 : Nat := 118140960795 + 13132 * 2 ^ 59
def prefixEnd_13132 : Nat := 4983230072969 + 3 ^ 40 * 13132 * 2
def baseEnd_13132 : Nat := 249741776109179803319

theorem tailTrace_13132 : CollatzResearch.WordTrace tailWord_13132 prefixEnd_13132 249741776109179803319 := by
  unfold tailWord_13132
  simp only [CollatzResearch.WordTrace]
  refine ⟨239481694216240806076825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 319308925621654408102433 239481694216240806076825)
  ·
    refine ⟨179611270662180604557619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239481694216240806076825 179611270662180604557619)
    ·
      refine ⟨269416905993270906836429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179611270662180604557619 269416905993270906836429)
      ·
        refine ⟨101031339747476590063661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269416905993270906836429 101031339747476590063661)
        ·
          refine ⟨37886752405303721273873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101031339747476590063661 37886752405303721273873)
          ·
            refine ⟨28415064303977790955405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37886752405303721273873 28415064303977790955405)
            ·
              refine ⟨10655649113991671608277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28415064303977790955405 10655649113991671608277)
              ·
                refine ⟨249741776109179803319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10655649113991671608277 249741776109179803319)
                ·
                  rfl

theorem cell23_13132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 7].length) (baseStart_13132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13132 prefixEnd_13132 := by exact prefixLift 13132
  have htrace : WordTrace (prefixWord ++ tailWord_13132) baseStart_13132 baseEnd_13132 := by
    simpa [prefixWord, tailWord_13132, baseEnd_13132] using wordTrace_append hprefix tailTrace_13132
  have hstable : (prefixWord ++ tailWord_13132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13132).length < 2 ^ (prefixWord ++ tailWord_13132).sum := by decide
  have hdescent : baseEnd_13132 < baseStart_13132 := by decide
  rcases family_descends (prefixWord ++ tailWord_13132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13143 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_13143 : Nat := 118140960795 + 13143 * 2 ^ 59
def prefixEnd_13143 : Nat := 4983230072969 + 3 ^ 40 * 13143 * 2
def baseEnd_13143 : Nat := 6748676242147311652063

theorem tailTrace_13143 : CollatzResearch.WordTrace tailWord_13143 prefixEnd_13143 6748676242147311652063 := by
  unfold tailWord_13143
  simp only [CollatzResearch.WordTrace]
  refine ⟨479364591392630490804083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 319576394261753660536055 479364591392630490804083)
  ·
    refine ⟨719046887088945736206125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479364591392630490804083 719046887088945736206125)
    ·
      refine ⟨269642582658354651077297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 719046887088945736206125 269642582658354651077297)
      ·
        refine ⟨202231936993765988307973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269642582658354651077297 202231936993765988307973)
        ·
          refine ⟨37918488186331122807745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202231936993765988307973 37918488186331122807745)
          ·
            refine ⟨28438866139748342105809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37918488186331122807745 28438866139748342105809)
            ·
              refine ⟨21329149604811256579357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28438866139748342105809 21329149604811256579357)
              ·
                refine ⟨7998431101804221217259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21329149604811256579357 7998431101804221217259)
                ·
                  refine ⟨11997646652706331825889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7998431101804221217259 11997646652706331825889)
                  ·
                    refine ⟨8998234989529748869417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11997646652706331825889 8998234989529748869417)
                    ·
                      refine ⟨6748676242147311652063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 8998234989529748869417 6748676242147311652063)
                      ·
                        rfl

theorem cell23_13143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_13143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13143 prefixEnd_13143 := by exact prefixLift 13143
  have htrace : WordTrace (prefixWord ++ tailWord_13143) baseStart_13143 baseEnd_13143 := by
    simpa [prefixWord, tailWord_13143, baseEnd_13143] using wordTrace_append hprefix tailTrace_13143
  have hstable : (prefixWord ++ tailWord_13143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13143).length < 2 ^ (prefixWord ++ tailWord_13143).sum := by decide
  have hdescent : baseEnd_13143 < baseStart_13143 := by decide
  rcases family_descends (prefixWord ++ tailWord_13143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13146 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_13146 : Nat := 118140960795 + 13146 * 2 ^ 59
def prefixEnd_13146 : Nat := 4983230072969 + 3 ^ 40 * 13146 * 2
def baseEnd_13146 : Nat := 6750216684110799914549

theorem tailTrace_13146 : CollatzResearch.WordTrace tailWord_13146 prefixEnd_13146 6750216684110799914549 := by
  unfold tailWord_13146
  simp only [CollatzResearch.WordTrace]
  refine ⟨119868502595440500790823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 319649340254508002108861 119868502595440500790823)
  ·
    refine ⟨179802753893160751186235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119868502595440500790823 179802753893160751186235)
    ·
      refine ⟨269704130839741126779353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179802753893160751186235 269704130839741126779353)
      ·
        refine ⟨202278098129805845084515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269704130839741126779353 202278098129805845084515)
        ·
          refine ⟨303417147194708767626773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202278098129805845084515 303417147194708767626773)
          ·
            refine ⟨14222678774751973482505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 303417147194708767626773 14222678774751973482505)
            ·
              refine ⟨10667009081063980111879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222678774751973482505 10667009081063980111879)
              ·
                refine ⟨16000513621595970167819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10667009081063980111879 16000513621595970167819)
                ·
                  refine ⟨24000770432393955251729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16000513621595970167819 24000770432393955251729)
                  ·
                    refine ⟨18000577824295466438797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24000770432393955251729 18000577824295466438797)
                    ·
                      refine ⟨6750216684110799914549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18000577824295466438797 6750216684110799914549)
                      ·
                        rfl

theorem cell23_13146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_13146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13146 prefixEnd_13146 := by exact prefixLift 13146
  have htrace : WordTrace (prefixWord ++ tailWord_13146) baseStart_13146 baseEnd_13146 := by
    simpa [prefixWord, tailWord_13146, baseEnd_13146] using wordTrace_append hprefix tailTrace_13146
  have hstable : (prefixWord ++ tailWord_13146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13146).length < 2 ^ (prefixWord ++ tailWord_13146).sum := by decide
  have hdescent : baseEnd_13146 < baseStart_13146 := by decide
  rcases family_descends (prefixWord ++ tailWord_13146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13159 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_13159 : Nat := 118140960795 + 13159 * 2 ^ 59
def prefixEnd_13159 : Nat := 4983230072969 + 3 ^ 40 * 13159 * 2
def baseEnd_13159 : Nat := 6756891932619249051989

theorem tailTrace_13159 : CollatzResearch.WordTrace tailWord_13159 prefixEnd_13159 6756891932619249051989 := by
  unfold tailWord_13159
  simp only [CollatzResearch.WordTrace]
  refine ⟨479948159334665223386531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 319965439556443482257687 479948159334665223386531)
  ·
    refine ⟨719922239001997835079797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 479948159334665223386531 719922239001997835079797)
    ·
      refine ⟨67492709906437297038731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 719922239001997835079797 67492709906437297038731)
      ·
        refine ⟨101239064859655945558097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67492709906437297038731 101239064859655945558097)
        ·
          refine ⟨75929298644741959168573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101239064859655945558097 75929298644741959168573)
          ·
            refine ⟨28473486991778234688215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75929298644741959168573 28473486991778234688215)
            ·
              refine ⟨42710230487667352032323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28473486991778234688215 42710230487667352032323)
              ·
                refine ⟨64065345731501028048485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42710230487667352032323 64065345731501028048485)
                ·
                  refine ⟨12012252324656442759091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64065345731501028048485 12012252324656442759091)
                  ·
                    refine ⟨18018378486984664138637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12012252324656442759091 18018378486984664138637)
                    ·
                      refine ⟨6756891932619249051989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18018378486984664138637 6756891932619249051989)
                      ·
                        rfl

theorem cell23_13159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_13159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13159 prefixEnd_13159 := by exact prefixLift 13159
  have htrace : WordTrace (prefixWord ++ tailWord_13159) baseStart_13159 baseEnd_13159 := by
    simpa [prefixWord, tailWord_13159, baseEnd_13159] using wordTrace_append hprefix tailTrace_13159
  have hstable : (prefixWord ++ tailWord_13159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13159).length < 2 ^ (prefixWord ++ tailWord_13159).sum := by decide
  have hdescent : baseEnd_13159 < baseStart_13159 := by decide
  rcases family_descends (prefixWord ++ tailWord_13159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13195 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_13195 : Nat := 118140960795 + 13195 * 2 ^ 59
def prefixEnd_13195 : Nat := 4983230072969 + 3 ^ 40 * 13195 * 2
def baseEnd_13195 : Nat := 6775377236181108201823

theorem tailTrace_13195 : CollatzResearch.WordTrace tailWord_13195 prefixEnd_13195 6775377236181108201823 := by
  unfold tailWord_13195
  simp only [CollatzResearch.WordTrace]
  refine ⟨481261187204243371697039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 320840791469495581131359 481261187204243371697039)
  ·
    refine ⟨721891780806365057545559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 481261187204243371697039 721891780806365057545559)
    ·
      refine ⟨1082837671209547586318339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721891780806365057545559 1082837671209547586318339)
      ·
        refine ⟨1624256506814321379477509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082837671209547586318339 1624256506814321379477509)
        ·
          refine ⟨304548095027685258652033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1624256506814321379477509 304548095027685258652033)
          ·
            refine ⟨228411071270763943989025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304548095027685258652033 228411071270763943989025)
            ·
              refine ⟨171308303453072957991769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228411071270763943989025 171308303453072957991769)
              ·
                refine ⟨128481227589804718493827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171308303453072957991769 128481227589804718493827)
                ·
                  refine ⟨192721841384707077740741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128481227589804718493827 192721841384707077740741)
                  ·
                    refine ⟨36135345259632577076389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 192721841384707077740741 36135345259632577076389)
                    ·
                      refine ⟨6775377236181108201823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 36135345259632577076389 6775377236181108201823)
                      ·
                        rfl

theorem cell23_13195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_13195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13195 prefixEnd_13195 := by exact prefixLift 13195
  have htrace : WordTrace (prefixWord ++ tailWord_13195) baseStart_13195 baseEnd_13195 := by
    simpa [prefixWord, tailWord_13195, baseEnd_13195] using wordTrace_append hprefix tailTrace_13195
  have hstable : (prefixWord ++ tailWord_13195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13195).length < 2 ^ (prefixWord ++ tailWord_13195).sum := by decide
  have hdescent : baseEnd_13195 < baseStart_13195 := by decide
  rcases family_descends (prefixWord ++ tailWord_13195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13233 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_13233 : Nat := 118140960795 + 13233 * 2 ^ 59
def prefixEnd_13233 : Nat := 4983230072969 + 3 ^ 40 * 13233 * 2
def baseEnd_13233 : Nat := 6794889501051959526649

theorem tailTrace_13233 : CollatzResearch.WordTrace tailWord_13233 prefixEnd_13233 6794889501051959526649 := by
  unfold tailWord_13233
  simp only [CollatzResearch.WordTrace]
  refine ⟨482647161066575861580353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 321764774044383907720235 482647161066575861580353)
  ·
    refine ⟨361985370799931896185265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 482647161066575861580353 361985370799931896185265)
    ·
      refine ⟨271489028099948922138949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361985370799931896185265 271489028099948922138949)
      ·
        refine ⟨50904192768740422901053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271489028099948922138949 50904192768740422901053)
        ·
          refine ⟨19089072288277658587895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50904192768740422901053 19089072288277658587895)
          ·
            refine ⟨28633608432416487881843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19089072288277658587895 28633608432416487881843)
            ·
              refine ⟨42950412648624731822765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28633608432416487881843 42950412648624731822765)
              ·
                refine ⟨16106404743234274433537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42950412648624731822765 16106404743234274433537)
                ·
                  refine ⟨12079803557425705825153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16106404743234274433537 12079803557425705825153)
                  ·
                    refine ⟨9059852668069279368865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12079803557425705825153 9059852668069279368865)
                    ·
                      refine ⟨6794889501051959526649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9059852668069279368865 6794889501051959526649)
                      ·
                        rfl

theorem cell23_13233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_13233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13233 prefixEnd_13233 := by exact prefixLift 13233
  have htrace : WordTrace (prefixWord ++ tailWord_13233) baseStart_13233 baseEnd_13233 := by
    simpa [prefixWord, tailWord_13233, baseEnd_13233] using wordTrace_append hprefix tailTrace_13233
  have hstable : (prefixWord ++ tailWord_13233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13233).length < 2 ^ (prefixWord ++ tailWord_13233).sum := by decide
  have hdescent : baseEnd_13233 < baseStart_13233 := by decide
  rcases family_descends (prefixWord ++ tailWord_13233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13235 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 7]
def baseStart_13235 : Nat := 118140960795 + 13235 * 2 ^ 59
def prefixEnd_13235 : Nat := 4983230072969 + 3 ^ 40 * 13235 * 2
def baseEnd_13235 : Nat := 2265305487453650567213

theorem tailTrace_13235 : CollatzResearch.WordTrace tailWord_13235 prefixEnd_13235 2265305487453650567213 := by
  unfold tailWord_13235
  simp only [CollatzResearch.WordTrace]
  refine ⟨482720107059330203153159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 321813404706220135435439 482720107059330203153159)
  ·
    refine ⟨724080160588995304729739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 482720107059330203153159 724080160588995304729739)
    ·
      refine ⟨1086120240883492957094609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724080160588995304729739 1086120240883492957094609)
      ·
        refine ⟨814590180662619717820957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086120240883492957094609 814590180662619717820957)
        ·
          refine ⟨305471317748482394182859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814590180662619717820957 305471317748482394182859)
          ·
            refine ⟨458206976622723591274289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305471317748482394182859 458206976622723591274289)
            ·
              refine ⟨343655232467042693455717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458206976622723591274289 343655232467042693455717)
              ·
                refine ⟨64435356087570505022947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343655232467042693455717 64435356087570505022947)
                ·
                  refine ⟨96653034131355757534421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64435356087570505022947 96653034131355757534421)
                  ·
                    refine ⟨2265305487453650567213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96653034131355757534421 2265305487453650567213)
                    ·
                      rfl

theorem cell23_13235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_13235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13235 prefixEnd_13235 := by exact prefixLift 13235
  have htrace : WordTrace (prefixWord ++ tailWord_13235) baseStart_13235 baseEnd_13235 := by
    simpa [prefixWord, tailWord_13235, baseEnd_13235] using wordTrace_append hprefix tailTrace_13235
  have hstable : (prefixWord ++ tailWord_13235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13235).length < 2 ^ (prefixWord ++ tailWord_13235).sum := by decide
  have hdescent : baseEnd_13235 < baseStart_13235 := by decide
  rcases family_descends (prefixWord ++ tailWord_13235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13262 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_13262 : Nat := 118140960795 + 13262 * 2 ^ 59
def prefixEnd_13262 : Nat := 4983230072969 + 3 ^ 40 * 13262 * 2
def baseEnd_13262 : Nat := 6809780440032346064015

theorem tailTrace_13262 : CollatzResearch.WordTrace tailWord_13262 prefixEnd_13262 6809780440032346064015 := by
  unfold tailWord_13262
  simp only [CollatzResearch.WordTrace]
  refine ⟨60463109745189226798255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 322469918641009209590693 60463109745189226798255)
  ·
    refine ⟨90694664617783840197383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60463109745189226798255 90694664617783840197383)
    ·
      refine ⟨136041996926675760296075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90694664617783840197383 136041996926675760296075)
      ·
        refine ⟨204062995390013640444113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136041996926675760296075 204062995390013640444113)
        ·
          refine ⟨153047246542510230333085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204062995390013640444113 153047246542510230333085)
          ·
            refine ⟨57392717453441336374907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153047246542510230333085 57392717453441336374907)
            ·
              refine ⟨86089076180162004562361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57392717453441336374907 86089076180162004562361)
              ·
                refine ⟨64566807135121503421771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86089076180162004562361 64566807135121503421771)
                ·
                  refine ⟨96850210702682255132657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64566807135121503421771 96850210702682255132657)
                  ·
                    refine ⟨72637658027011691349493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96850210702682255132657 72637658027011691349493)
                    ·
                      refine ⟨6809780440032346064015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 72637658027011691349493 6809780440032346064015)
                      ·
                        rfl

theorem cell23_13262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_13262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13262 prefixEnd_13262 := by exact prefixLift 13262
  have htrace : WordTrace (prefixWord ++ tailWord_13262) baseStart_13262 baseEnd_13262 := by
    simpa [prefixWord, tailWord_13262, baseEnd_13262] using wordTrace_append hprefix tailTrace_13262
  have hstable : (prefixWord ++ tailWord_13262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13262).length < 2 ^ (prefixWord ++ tailWord_13262).sum := by decide
  have hdescent : baseEnd_13262 < baseStart_13262 := by decide
  rcases family_descends (prefixWord ++ tailWord_13262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13346 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_13346 : Nat := 118140960795 + 13346 * 2 ^ 59
def prefixEnd_13346 : Nat := 4983230072969 + 3 ^ 40 * 13346 * 2
def baseEnd_13346 : Nat := 761434757223335268181

theorem tailTrace_13346 : CollatzResearch.WordTrace tailWord_13346 prefixEnd_13346 761434757223335268181 := by
  unfold tailWord_13346
  simp only [CollatzResearch.WordTrace]
  refine ⟨121692152414299040110973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 324512406438130773629261 121692152414299040110973)
  ·
    refine ⟨45634557155362140041615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121692152414299040110973 45634557155362140041615)
    ·
      refine ⟨68451835733043210062423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45634557155362140041615 68451835733043210062423)
      ·
        refine ⟨102677753599564815093635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68451835733043210062423 102677753599564815093635)
        ·
          refine ⟨154016630399347222640453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102677753599564815093635 154016630399347222640453)
          ·
            refine ⟨28878118199877604245085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154016630399347222640453 28878118199877604245085)
            ·
              refine ⟨10829294324954101591907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28878118199877604245085 10829294324954101591907)
              ·
                refine ⟨16243941487431152387861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10829294324954101591907 16243941487431152387861)
                ·
                  refine ⟨761434757223335268181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16243941487431152387861 761434757223335268181)
                  ·
                    rfl

theorem cell23_13346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_13346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13346 prefixEnd_13346 := by exact prefixLift 13346
  have htrace : WordTrace (prefixWord ++ tailWord_13346) baseStart_13346 baseEnd_13346 := by
    simpa [prefixWord, tailWord_13346, baseEnd_13346] using wordTrace_append hprefix tailTrace_13346
  have hstable : (prefixWord ++ tailWord_13346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13346).length < 2 ^ (prefixWord ++ tailWord_13346).sum := by decide
  have hdescent : baseEnd_13346 < baseStart_13346 := by decide
  rcases family_descends (prefixWord ++ tailWord_13346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13349 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_13349 : Nat := 118140960795 + 13349 * 2 ^ 59
def prefixEnd_13349 : Nat := 4983230072969 + 3 ^ 40 * 13349 * 2
def baseEnd_13349 : Nat := 6854453256973505676115

theorem tailTrace_13349 : CollatzResearch.WordTrace tailWord_13349 prefixEnd_13349 6854453256973505676115 := by
  unfold tailWord_13349
  simp only [CollatzResearch.WordTrace]
  refine ⟨486878028646327672803101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 324585352430885115202067 486878028646327672803101)
  ·
    refine ⟨182579260742372877301163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 486878028646327672803101 182579260742372877301163)
    ·
      refine ⟨273868891113559315951745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182579260742372877301163 273868891113559315951745)
      ·
        refine ⟨205401668335169486963809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273868891113559315951745 205401668335169486963809)
        ·
          refine ⟨154051251251377115222857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205401668335169486963809 154051251251377115222857)
          ·
            refine ⟨115538438438532836417143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154051251251377115222857 115538438438532836417143)
            ·
              refine ⟨173307657657799254625715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115538438438532836417143 173307657657799254625715)
              ·
                refine ⟨259961486486698881938573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173307657657799254625715 259961486486698881938573)
                ·
                  refine ⟨97485557432512080726965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259961486486698881938573 97485557432512080726965)
                  ·
                    refine ⟨9139271009298007568153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97485557432512080726965 9139271009298007568153)
                    ·
                      refine ⟨6854453256973505676115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9139271009298007568153 6854453256973505676115)
                      ·
                        rfl

theorem cell23_13349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_13349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13349 prefixEnd_13349 := by exact prefixLift 13349
  have htrace : WordTrace (prefixWord ++ tailWord_13349) baseStart_13349 baseEnd_13349 := by
    simpa [prefixWord, tailWord_13349, baseEnd_13349] using wordTrace_append hprefix tailTrace_13349
  have hstable : (prefixWord ++ tailWord_13349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13349).length < 2 ^ (prefixWord ++ tailWord_13349).sum := by decide
  have hdescent : baseEnd_13349 < baseStart_13349 := by decide
  rcases family_descends (prefixWord ++ tailWord_13349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13379 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 4]
def baseStart_13379 : Nat := 118140960795 + 13379 * 2 ^ 59
def prefixEnd_13379 : Nat := 4983230072969 + 3 ^ 40 * 13379 * 2
def baseEnd_13379 : Nat := 6869857676608388300977

theorem tailTrace_13379 : CollatzResearch.WordTrace tailWord_13379 prefixEnd_13379 6869857676608388300977 := by
  unfold tailWord_13379
  simp only [CollatzResearch.WordTrace]
  refine ⟨487972218537642796395191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325314812358428530930127 487972218537642796395191)
  ·
    refine ⟨731958327806464194592787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487972218537642796395191 731958327806464194592787)
    ·
      refine ⟨1097937491709696291889181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731958327806464194592787 1097937491709696291889181)
      ·
        refine ⟨411726559391136109458443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1097937491709696291889181 411726559391136109458443)
        ·
          refine ⟨617589839086704164187665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411726559391136109458443 617589839086704164187665)
          ·
            refine ⟨463192379315028123140749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617589839086704164187665 463192379315028123140749)
            ·
              refine ⟨173697142243135546177781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463192379315028123140749 173697142243135546177781)
              ·
                refine ⟨16284107085293957454167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173697142243135546177781 16284107085293957454167)
                ·
                  refine ⟨24426160627940936181251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16284107085293957454167 24426160627940936181251)
                  ·
                    refine ⟨36639240941911404271877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24426160627940936181251 36639240941911404271877)
                    ·
                      refine ⟨6869857676608388300977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 36639240941911404271877 6869857676608388300977)
                      ·
                        rfl

theorem cell23_13379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_13379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13379 prefixEnd_13379 := by exact prefixLift 13379
  have htrace : WordTrace (prefixWord ++ tailWord_13379) baseStart_13379 baseEnd_13379 := by
    simpa [prefixWord, tailWord_13379, baseEnd_13379] using wordTrace_append hprefix tailTrace_13379
  have hstable : (prefixWord ++ tailWord_13379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13379).length < 2 ^ (prefixWord ++ tailWord_13379).sum := by decide
  have hdescent : baseEnd_13379 < baseStart_13379 := by decide
  rcases family_descends (prefixWord ++ tailWord_13379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13390 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3]
def baseStart_13390 : Nat := 118140960795 + 13390 * 2 ^ 59
def prefixEnd_13390 : Nat := 4983230072969 + 3 ^ 40 * 13390 * 2
def baseEnd_13390 : Nat := 6875505963807845263427

theorem tailTrace_13390 : CollatzResearch.WordTrace tailWord_13390 prefixEnd_13390 6875505963807845263427 := by
  unfold tailWord_13390
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046677687223959380703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 325582280998527783363749 61046677687223959380703)
  ·
    refine ⟨91570016530835939071055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61046677687223959380703 91570016530835939071055)
    ·
      refine ⟨137355024796253908606583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91570016530835939071055 137355024796253908606583)
      ·
        refine ⟨206032537194380862909875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137355024796253908606583 206032537194380862909875)
        ·
          refine ⟨309048805791571294364813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206032537194380862909875 309048805791571294364813)
          ·
            refine ⟨115893302171839235386805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309048805791571294364813 115893302171839235386805)
            ·
              refine ⟨10864997078609928317513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115893302171839235386805 10864997078609928317513)
              ·
                refine ⟨8148747808957446238135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864997078609928317513 8148747808957446238135)
                ·
                  refine ⟨12223121713436169357203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148747808957446238135 12223121713436169357203)
                  ·
                    refine ⟨18334682570154254035805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12223121713436169357203 18334682570154254035805)
                    ·
                      refine ⟨6875505963807845263427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18334682570154254035805 6875505963807845263427)
                      ·
                        rfl

theorem cell23_13390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_13390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13390 prefixEnd_13390 := by exact prefixLift 13390
  have htrace : WordTrace (prefixWord ++ tailWord_13390) baseStart_13390 baseEnd_13390 := by
    simpa [prefixWord, tailWord_13390, baseEnd_13390] using wordTrace_append hprefix tailTrace_13390
  have hstable : (prefixWord ++ tailWord_13390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13390).length < 2 ^ (prefixWord ++ tailWord_13390).sum := by decide
  have hdescent : baseEnd_13390 < baseStart_13390 := by decide
  rcases family_descends (prefixWord ++ tailWord_13390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13399 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_13399 : Nat := 118140960795 + 13399 * 2 ^ 59
def prefixEnd_13399 : Nat := 4983230072969 + 3 ^ 40 * 13399 * 2
def baseEnd_13399 : Nat := 6880127289698310050885

theorem tailTrace_13399 : CollatzResearch.WordTrace tailWord_13399 prefixEnd_13399 6880127289698310050885 := by
  unfold tailWord_13399
  simp only [CollatzResearch.WordTrace]
  refine ⟨488701678465186212123251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 325801118976790808082167 488701678465186212123251)
  ·
    refine ⟨733052517697779318184877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 488701678465186212123251 733052517697779318184877)
    ·
      refine ⟨274894694136667244319329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 733052517697779318184877 274894694136667244319329)
      ·
        refine ⟨206171020602500433239497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274894694136667244319329 206171020602500433239497)
        ·
          refine ⟨154628265451875324929623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206171020602500433239497 154628265451875324929623)
          ·
            refine ⟨231942398177812987394435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154628265451875324929623 231942398177812987394435)
            ·
              refine ⟨347913597266719481091653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231942398177812987394435 347913597266719481091653)
              ·
                refine ⟨65233799487509902704685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347913597266719481091653 65233799487509902704685)
                ·
                  refine ⟨24462674807816213514257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65233799487509902704685 24462674807816213514257)
                  ·
                    refine ⟨18347006105862160135693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24462674807816213514257 18347006105862160135693)
                    ·
                      refine ⟨6880127289698310050885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18347006105862160135693 6880127289698310050885)
                      ·
                        rfl

theorem cell23_13399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_13399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13399 prefixEnd_13399 := by exact prefixLift 13399
  have htrace : WordTrace (prefixWord ++ tailWord_13399) baseStart_13399 baseEnd_13399 := by
    simpa [prefixWord, tailWord_13399, baseEnd_13399] using wordTrace_append hprefix tailTrace_13399
  have hstable : (prefixWord ++ tailWord_13399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13399).length < 2 ^ (prefixWord ++ tailWord_13399).sum := by decide
  have hdescent : baseEnd_13399 < baseStart_13399 := by decide
  rcases family_descends (prefixWord ++ tailWord_13399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13433 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 1, 1, 5]
def baseStart_13433 : Nat := 118140960795 + 13433 * 2 ^ 59
def prefixEnd_13433 : Nat := 4983230072969 + 3 ^ 40 * 13433 * 2
def baseEnd_13433 : Nat := 6897585631951177025729

theorem tailTrace_13433 : CollatzResearch.WordTrace tailWord_13433 prefixEnd_13433 6897585631951177025729 := by
  unfold tailWord_13433
  simp only [CollatzResearch.WordTrace]
  refine ⟨489941760342010018860953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 326627840228006679240635 489941760342010018860953)
  ·
    refine ⟨367456320256507514145715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 489941760342010018860953 367456320256507514145715)
    ·
      refine ⟨551184480384761271218573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367456320256507514145715 551184480384761271218573)
      ·
        refine ⟨206694180144285476706965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551184480384761271218573 206694180144285476706965)
        ·
          refine ⟨9688789694263381720639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206694180144285476706965 9688789694263381720639)
          ·
            refine ⟨14533184541395072580959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688789694263381720639 14533184541395072580959)
            ·
              refine ⟨21799776812092608871439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14533184541395072580959 21799776812092608871439)
              ·
                refine ⟨32699665218138913307159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21799776812092608871439 32699665218138913307159)
                ·
                  refine ⟨49049497827208369960739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32699665218138913307159 49049497827208369960739)
                  ·
                    refine ⟨73574246740812554941109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49049497827208369960739 73574246740812554941109)
                    ·
                      refine ⟨6897585631951177025729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 73574246740812554941109 6897585631951177025729)
                      ·
                        rfl

theorem cell23_13433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_13433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13433 prefixEnd_13433 := by exact prefixLift 13433
  have htrace : WordTrace (prefixWord ++ tailWord_13433) baseStart_13433 baseEnd_13433 := by
    simpa [prefixWord, tailWord_13433, baseEnd_13433] using wordTrace_append hprefix tailTrace_13433
  have hstable : (prefixWord ++ tailWord_13433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13433).length < 2 ^ (prefixWord ++ tailWord_13433).sum := by decide
  have hdescent : baseEnd_13433 < baseStart_13433 := by decide
  rcases family_descends (prefixWord ++ tailWord_13433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13463 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_13463 : Nat := 118140960795 + 13463 * 2 ^ 59
def prefixEnd_13463 : Nat := 4983230072969 + 3 ^ 40 * 13463 * 2
def baseEnd_13463 : Nat := 6912990051586059650591

theorem tailTrace_13463 : CollatzResearch.WordTrace tailWord_13463 prefixEnd_13463 6912990051586059650591 := by
  unfold tailWord_13463
  simp only [CollatzResearch.WordTrace]
  refine ⟨491035950233325142453043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 327357300155550094968695 491035950233325142453043)
  ·
    refine ⟨736553925349987713679565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491035950233325142453043 736553925349987713679565)
    ·
      refine ⟨276207722006245392629837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 736553925349987713679565 276207722006245392629837)
      ·
        refine ⟨103577895752342022236189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276207722006245392629837 103577895752342022236189)
        ·
          refine ⟨38841710907128258338571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103577895752342022236189 38841710907128258338571)
          ·
            refine ⟨58262566360692387507857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38841710907128258338571 58262566360692387507857)
            ·
              refine ⟨43696924770519290630893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58262566360692387507857 43696924770519290630893)
              ·
                refine ⟨16386346788944733986585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43696924770519290630893 16386346788944733986585)
                ·
                  refine ⟨12289760091708550489939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16386346788944733986585 12289760091708550489939)
                  ·
                    refine ⟨18434640137562825734909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12289760091708550489939 18434640137562825734909)
                    ·
                      refine ⟨6912990051586059650591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18434640137562825734909 6912990051586059650591)
                      ·
                        rfl

theorem cell23_13463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_13463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13463 prefixEnd_13463 := by exact prefixLift 13463
  have htrace : WordTrace (prefixWord ++ tailWord_13463) baseStart_13463 baseEnd_13463 := by
    simpa [prefixWord, tailWord_13463, baseEnd_13463] using wordTrace_append hprefix tailTrace_13463
  have hstable : (prefixWord ++ tailWord_13463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13463).length < 2 ^ (prefixWord ++ tailWord_13463).sum := by decide
  have hdescent : baseEnd_13463 < baseStart_13463 := by decide
  rcases family_descends (prefixWord ++ tailWord_13463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13469 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_13469 : Nat := 118140960795 + 13469 * 2 ^ 59
def prefixEnd_13469 : Nat := 4983230072969 + 3 ^ 40 * 13469 * 2
def baseEnd_13469 : Nat := 6916070935513036175563

theorem tailTrace_13469 : CollatzResearch.WordTrace tailWord_13469 prefixEnd_13469 6916070935513036175563 := by
  unfold tailWord_13469
  simp only [CollatzResearch.WordTrace]
  refine ⟨491254788211588167171461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 327503192141058778114307 491254788211588167171461)
  ·
    refine ⟨92110272789672781344649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 491254788211588167171461 92110272789672781344649)
    ·
      refine ⟨69082704592254586008487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92110272789672781344649 69082704592254586008487)
      ·
        refine ⟨103624056888381879012731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69082704592254586008487 103624056888381879012731)
        ·
          refine ⟨155436085332572818519097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103624056888381879012731 155436085332572818519097)
          ·
            refine ⟨116577063999429613889323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155436085332572818519097 116577063999429613889323)
            ·
              refine ⟨174865595999144420833985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116577063999429613889323 174865595999144420833985)
              ·
                refine ⟨131149196999358315625489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174865595999144420833985 131149196999358315625489)
                ·
                  refine ⟨98361897749518736719117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131149196999358315625489 98361897749518736719117)
                  ·
                    refine ⟨36885711656069526269669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98361897749518736719117 36885711656069526269669)
                    ·
                      refine ⟨6916070935513036175563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 36885711656069526269669 6916070935513036175563)
                      ·
                        rfl

theorem cell23_13469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_13469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13469 prefixEnd_13469 := by exact prefixLift 13469
  have htrace : WordTrace (prefixWord ++ tailWord_13469) baseStart_13469 baseEnd_13469 := by
    simpa [prefixWord, tailWord_13469, baseEnd_13469] using wordTrace_append hprefix tailTrace_13469
  have hstable : (prefixWord ++ tailWord_13469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13469).length < 2 ^ (prefixWord ++ tailWord_13469).sum := by decide
  have hdescent : baseEnd_13469 < baseStart_13469 := by decide
  rcases family_descends (prefixWord ++ tailWord_13469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13473 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_13473 : Nat := 118140960795 + 13473 * 2 ^ 59
def prefixEnd_13473 : Nat := 4983230072969 + 3 ^ 40 * 13473 * 2
def baseEnd_13473 : Nat := 6918124858131020525545

theorem tailTrace_13473 : CollatzResearch.WordTrace tailWord_13473 prefixEnd_13473 6918124858131020525545 := by
  unfold tailWord_13473
  simp only [CollatzResearch.WordTrace]
  refine ⟨491400680197096850317073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 327600453464731233544715 491400680197096850317073)
  ·
    refine ⟨368550510147822637737805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491400680197096850317073 368550510147822637737805)
    ·
      refine ⟨138206441305433489151677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368550510147822637737805 138206441305433489151677)
      ·
        refine ⟨51827415489537558431879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138206441305433489151677 51827415489537558431879)
        ·
          refine ⟨77741123234306337647819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51827415489537558431879 77741123234306337647819)
          ·
            refine ⟨116611684851459506471729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77741123234306337647819 116611684851459506471729)
            ·
              refine ⟨87458763638594629853797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116611684851459506471729 87458763638594629853797)
              ·
                refine ⟨16398518182236493097587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87458763638594629853797 16398518182236493097587)
                ·
                  refine ⟨24597777273354739646381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16398518182236493097587 24597777273354739646381)
                  ·
                    refine ⟨9224166477508027367393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24597777273354739646381 9224166477508027367393)
                    ·
                      refine ⟨6918124858131020525545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9224166477508027367393 6918124858131020525545)
                      ·
                        rfl

theorem cell23_13473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_13473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13473 prefixEnd_13473 := by exact prefixLift 13473
  have htrace : WordTrace (prefixWord ++ tailWord_13473) baseStart_13473 baseEnd_13473 := by
    simpa [prefixWord, tailWord_13473, baseEnd_13473] using wordTrace_append hprefix tailTrace_13473
  have hstable : (prefixWord ++ tailWord_13473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13473).length < 2 ^ (prefixWord ++ tailWord_13473).sum := by decide
  have hdescent : baseEnd_13473 < baseStart_13473 := by decide
  rcases family_descends (prefixWord ++ tailWord_13473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13490 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2]
def baseStart_13490 : Nat := 118140960795 + 13490 * 2 ^ 59
def prefixEnd_13490 : Nat := 4983230072969 + 3 ^ 40 * 13490 * 2
def baseEnd_13490 : Nat := 6926854029257454012967

theorem tailTrace_13490 : CollatzResearch.WordTrace tailWord_13490 prefixEnd_13490 6926854029257454012967 := by
  unfold tailWord_13490
  simp only [CollatzResearch.WordTrace]
  refine ⟨123005180283877188421481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 328013814090339169123949 123005180283877188421481)
  ·
    refine ⟨92253885212907891316111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123005180283877188421481 92253885212907891316111)
    ·
      refine ⟨138380827819361836974167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92253885212907891316111 138380827819361836974167)
      ·
        refine ⟨207571241729042755461251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138380827819361836974167 207571241729042755461251)
        ·
          refine ⟨311356862593564133191877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207571241729042755461251 311356862593564133191877)
          ·
            refine ⟨58379411736293274973477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311356862593564133191877 58379411736293274973477)
            ·
              refine ⟨10946139700554989057527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58379411736293274973477 10946139700554989057527)
              ·
                refine ⟨16419209550832483586291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946139700554989057527 16419209550832483586291)
                ·
                  refine ⟨24628814326248725379437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16419209550832483586291 24628814326248725379437)
                  ·
                    refine ⟨9235805372343272017289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24628814326248725379437 9235805372343272017289)
                    ·
                      refine ⟨6926854029257454012967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9235805372343272017289 6926854029257454012967)
                      ·
                        rfl

theorem cell23_13490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_13490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13490 prefixEnd_13490 := by exact prefixLift 13490
  have htrace : WordTrace (prefixWord ++ tailWord_13490) baseStart_13490 baseEnd_13490 := by
    simpa [prefixWord, tailWord_13490, baseEnd_13490] using wordTrace_append hprefix tailTrace_13490
  have hstable : (prefixWord ++ tailWord_13490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13490).length < 2 ^ (prefixWord ++ tailWord_13490).sum := by decide
  have hdescent : baseEnd_13490 < baseStart_13490 := by decide
  rcases family_descends (prefixWord ++ tailWord_13490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13519 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_13519 : Nat := 118140960795 + 13519 * 2 ^ 59
def prefixEnd_13519 : Nat := 4983230072969 + 3 ^ 40 * 13519 * 2
def baseEnd_13519 : Nat := 6941744968237840550333

theorem tailTrace_13519 : CollatzResearch.WordTrace tailWord_13519 prefixEnd_13519 6941744968237840550333 := by
  unfold tailWord_13519
  simp only [CollatzResearch.WordTrace]
  refine ⟨493078438030446706491611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 328718958686964470994407 493078438030446706491611)
  ·
    refine ⟨739617657045670059737417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 493078438030446706491611 739617657045670059737417)
    ·
      refine ⟨554713242784252544803063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 739617657045670059737417 554713242784252544803063)
      ·
        refine ⟨832069864176378817204595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554713242784252544803063 832069864176378817204595)
        ·
          refine ⟨1248104796264568225806893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832069864176378817204595 1248104796264568225806893)
          ·
            refine ⟨468039298599213084677585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248104796264568225806893 468039298599213084677585)
            ·
              refine ⟨351029473949409813508189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468039298599213084677585 351029473949409813508189)
              ·
                refine ⟨131636052731028680065571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351029473949409813508189 131636052731028680065571)
                ·
                  refine ⟨197454079096543020098357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131636052731028680065571 197454079096543020098357)
                  ·
                    refine ⟨18511319915300908134221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 197454079096543020098357 18511319915300908134221)
                    ·
                      refine ⟨6941744968237840550333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18511319915300908134221 6941744968237840550333)
                      ·
                        rfl

theorem cell23_13519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_13519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13519 prefixEnd_13519 := by exact prefixLift 13519
  have htrace : WordTrace (prefixWord ++ tailWord_13519) baseStart_13519 baseEnd_13519 := by
    simpa [prefixWord, tailWord_13519, baseEnd_13519] using wordTrace_append hprefix tailTrace_13519
  have hstable : (prefixWord ++ tailWord_13519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13519).length < 2 ^ (prefixWord ++ tailWord_13519).sum := by decide
  have hdescent : baseEnd_13519 < baseStart_13519 := by decide
  rcases family_descends (prefixWord ++ tailWord_13519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13566 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_13566 : Nat := 118140960795 + 13566 * 2 ^ 59
def prefixEnd_13566 : Nat := 4983230072969 + 3 ^ 40 * 13566 * 2
def baseEnd_13566 : Nat := 6965878558999156662617

theorem tailTrace_13566 : CollatzResearch.WordTrace tailWord_13566 prefixEnd_13566 6965878558999156662617 := by
  unfold tailWord_13566
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849083607521716681569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 329861779240115822301701 61849083607521716681569)
  ·
    refine ⟨46386812705641287511177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61849083607521716681569 46386812705641287511177)
    ·
      refine ⟨34790109529230965633383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46386812705641287511177 34790109529230965633383)
      ·
        refine ⟨52185164293846448450075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34790109529230965633383 52185164293846448450075)
        ·
          refine ⟨78277746440769672675113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52185164293846448450075 78277746440769672675113)
          ·
            refine ⟨58708309830577254506335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78277746440769672675113 58708309830577254506335)
            ·
              refine ⟨88062464745865881759503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58708309830577254506335 88062464745865881759503)
              ·
                refine ⟨132093697118798822639255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88062464745865881759503 132093697118798822639255)
                ·
                  refine ⟨198140545678198233958883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132093697118798822639255 198140545678198233958883)
                  ·
                    refine ⟨297210818517297350938325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198140545678198233958883 297210818517297350938325)
                    ·
                      refine ⟨6965878558999156662617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 297210818517297350938325 6965878558999156662617)
                      ·
                        rfl

theorem cell23_13566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_13566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13566 prefixEnd_13566 := by exact prefixLift 13566
  have htrace : WordTrace (prefixWord ++ tailWord_13566) baseStart_13566 baseEnd_13566 := by
    simpa [prefixWord, tailWord_13566, baseEnd_13566] using wordTrace_append hprefix tailTrace_13566
  have hstable : (prefixWord ++ tailWord_13566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13566).length < 2 ^ (prefixWord ++ tailWord_13566).sum := by decide
  have hdescent : baseEnd_13566 < baseStart_13566 := by decide
  rcases family_descends (prefixWord ++ tailWord_13566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13589 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_13589 : Nat := 118140960795 + 13589 * 2 ^ 59
def prefixEnd_13589 : Nat := 4983230072969 + 3 ^ 40 * 13589 * 2
def baseEnd_13589 : Nat := 6977688614052566675011

theorem tailTrace_13589 : CollatzResearch.WordTrace tailWord_13589 prefixEnd_13589 6977688614052566675011 := by
  unfold tailWord_13589
  simp only [CollatzResearch.WordTrace]
  refine ⟨495631547776848661539821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 330421031851232441026547 495631547776848661539821)
  ·
    refine ⟨185861830416318248077433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 495631547776848661539821 185861830416318248077433)
    ·
      refine ⟨139396372812238686058075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185861830416318248077433 139396372812238686058075)
      ·
        refine ⟨209094559218358029087113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139396372812238686058075 209094559218358029087113)
        ·
          refine ⟨156820919413768521815335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209094559218358029087113 156820919413768521815335)
          ·
            refine ⟨235231379120652782723003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156820919413768521815335 235231379120652782723003)
            ·
              refine ⟨352847068680979174084505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235231379120652782723003 352847068680979174084505)
              ·
                refine ⟨264635301510734380563379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352847068680979174084505 264635301510734380563379)
                ·
                  refine ⟨396952952266101570845069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264635301510734380563379 396952952266101570845069)
                  ·
                    refine ⟨148857357099788089066901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 396952952266101570845069 148857357099788089066901)
                    ·
                      refine ⟨6977688614052566675011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 148857357099788089066901 6977688614052566675011)
                      ·
                        rfl

theorem cell23_13589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_13589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13589 prefixEnd_13589 := by exact prefixLift 13589
  have htrace : WordTrace (prefixWord ++ tailWord_13589) baseStart_13589 baseEnd_13589 := by
    simpa [prefixWord, tailWord_13589, baseEnd_13589] using wordTrace_append hprefix tailTrace_13589
  have hstable : (prefixWord ++ tailWord_13589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13589).length < 2 ^ (prefixWord ++ tailWord_13589).sum := by decide
  have hdescent : baseEnd_13589 < baseStart_13589 := by decide
  rcases family_descends (prefixWord ++ tailWord_13589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13596 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_13596 : Nat := 118140960795 + 13596 * 2 ^ 59
def prefixEnd_13596 : Nat := 4983230072969 + 3 ^ 40 * 13596 * 2
def baseEnd_13596 : Nat := 6981282978634039287479

theorem tailTrace_13596 : CollatzResearch.WordTrace tailWord_13596 prefixEnd_13596 6981282978634039287479 := by
  unfold tailWord_13596
  simp only [CollatzResearch.WordTrace]
  refine ⟨247943429375744428522321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 330591239167659238029761 247943429375744428522321)
  ·
    refine ⟨185957572031808321391741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 247943429375744428522321 185957572031808321391741)
    ·
      refine ⟨69734089511928120521903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185957572031808321391741 69734089511928120521903)
      ·
        refine ⟨104601134267892180782855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69734089511928120521903 104601134267892180782855)
        ·
          refine ⟨156901701401838271174283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104601134267892180782855 156901701401838271174283)
          ·
            refine ⟨235352552102757406761425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156901701401838271174283 235352552102757406761425)
            ·
              refine ⟨176514414077068055071069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235352552102757406761425 176514414077068055071069)
              ·
                refine ⟨66192905278900520651651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176514414077068055071069 66192905278900520651651)
                ·
                  refine ⟨99289357918350780977477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66192905278900520651651 99289357918350780977477)
                  ·
                    refine ⟨18616754609690771433277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99289357918350780977477 18616754609690771433277)
                    ·
                      refine ⟨6981282978634039287479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18616754609690771433277 6981282978634039287479)
                      ·
                        rfl

theorem cell23_13596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_13596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13596 prefixEnd_13596 := by exact prefixLift 13596
  have htrace : WordTrace (prefixWord ++ tailWord_13596) baseStart_13596 baseEnd_13596 := by
    simpa [prefixWord, tailWord_13596, baseEnd_13596] using wordTrace_append hprefix tailTrace_13596
  have hstable : (prefixWord ++ tailWord_13596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13596).length < 2 ^ (prefixWord ++ tailWord_13596).sum := by decide
  have hdescent : baseEnd_13596 < baseStart_13596 := by decide
  rcases family_descends (prefixWord ++ tailWord_13596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13616 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 6]
def baseStart_13616 : Nat := 118140960795 + 13616 * 2 ^ 59
def prefixEnd_13616 : Nat := 4983230072969 + 3 ^ 40 * 13616 * 2
def baseEnd_13616 : Nat := 776839176858217893043

theorem tailTrace_13616 : CollatzResearch.WordTrace tailWord_13616 prefixEnd_13616 776839176858217893043 := by
  unfold tailWord_13616
  simp only [CollatzResearch.WordTrace]
  refine ⟨248308159339516136386351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 331077545786021515181801 248308159339516136386351)
  ·
    refine ⟨372462239009274204579527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248308159339516136386351 372462239009274204579527)
    ·
      refine ⟨558693358513911306869291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372462239009274204579527 558693358513911306869291)
      ·
        refine ⟨838040037770866960303937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558693358513911306869291 838040037770866960303937)
        ·
          refine ⟨628530028328150220227953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838040037770866960303937 628530028328150220227953)
          ·
            refine ⟨471397521246112665170965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628530028328150220227953 471397521246112665170965)
            ·
              refine ⟨22096758808411531179889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471397521246112665170965 22096758808411531179889)
              ·
                refine ⟨16572569106308648384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22096758808411531179889 16572569106308648384917)
                ·
                  refine ⟨776839176858217893043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16572569106308648384917 776839176858217893043)
                  ·
                    rfl

theorem cell23_13616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_13616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13616 prefixEnd_13616 := by exact prefixLift 13616
  have htrace : WordTrace (prefixWord ++ tailWord_13616) baseStart_13616 baseEnd_13616 := by
    simpa [prefixWord, tailWord_13616, baseEnd_13616] using wordTrace_append hprefix tailTrace_13616
  have hstable : (prefixWord ++ tailWord_13616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13616).length < 2 ^ (prefixWord ++ tailWord_13616).sum := by decide
  have hdescent : baseEnd_13616 < baseStart_13616 := by decide
  rcases family_descends (prefixWord ++ tailWord_13616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13633 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 6]
def baseStart_13633 : Nat := 118140960795 + 13633 * 2 ^ 59
def prefixEnd_13633 : Nat := 4983230072969 + 3 ^ 40 * 13633 * 2
def baseEnd_13633 : Nat := 777809084761154947201

theorem tailTrace_13633 : CollatzResearch.WordTrace tailWord_13633 prefixEnd_13633 777809084761154947201 := by
  unfold tailWord_13633
  simp only [CollatzResearch.WordTrace]
  refine ⟨497236359617444176141553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 331490906411629450761035 497236359617444176141553)
  ·
    refine ⟨372927269713083132106165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 497236359617444176141553 372927269713083132106165)
    ·
      refine ⟨34961931535601543634953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372927269713083132106165 34961931535601543634953)
      ·
        refine ⟨26221448651701157726215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34961931535601543634953 26221448651701157726215)
        ·
          refine ⟨39332172977551736589323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26221448651701157726215 39332172977551736589323)
          ·
            refine ⟨58998259466327604883985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39332172977551736589323 58998259466327604883985)
            ·
              refine ⟨44248694599745703662989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58998259466327604883985 44248694599745703662989)
              ·
                refine ⟨16593260474904638873621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44248694599745703662989 16593260474904638873621)
                ·
                  refine ⟨777809084761154947201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16593260474904638873621 777809084761154947201)
                  ·
                    rfl

theorem cell23_13633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 6].length) (baseStart_13633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13633 prefixEnd_13633 := by exact prefixLift 13633
  have htrace : WordTrace (prefixWord ++ tailWord_13633) baseStart_13633 baseEnd_13633 := by
    simpa [prefixWord, tailWord_13633, baseEnd_13633] using wordTrace_append hprefix tailTrace_13633
  have hstable : (prefixWord ++ tailWord_13633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13633).length < 2 ^ (prefixWord ++ tailWord_13633).sum := by decide
  have hdescent : baseEnd_13633 < baseStart_13633 := by decide
  rcases family_descends (prefixWord ++ tailWord_13633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13646 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_13646 : Nat := 118140960795 + 13646 * 2 ^ 59
def prefixEnd_13646 : Nat := 4983230072969 + 3 ^ 40 * 13646 * 2
def baseEnd_13646 : Nat := 2335652337119614554083

theorem tailTrace_13646 : CollatzResearch.WordTrace tailWord_13646 prefixEnd_13646 2335652337119614554083 := by
  unfold tailWord_13646
  simp only [CollatzResearch.WordTrace]
  refine ⟨62213813571293424545599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 331807005713564930909861 62213813571293424545599)
  ·
    refine ⟨93320720356940136818399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62213813571293424545599 93320720356940136818399)
    ·
      refine ⟨139981080535410205227599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93320720356940136818399 139981080535410205227599)
      ·
        refine ⟨209971620803115307841399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139981080535410205227599 209971620803115307841399)
        ·
          refine ⟨314957431204672961762099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209971620803115307841399 314957431204672961762099)
          ·
            refine ⟨472436146807009442643149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314957431204672961762099 472436146807009442643149)
            ·
              refine ⟨177163555052628540991181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472436146807009442643149 177163555052628540991181)
              ·
                refine ⟨66436333144735702871693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177163555052628540991181 66436333144735702871693)
                ·
                  refine ⟨24913624929275888576885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66436333144735702871693 24913624929275888576885)
                  ·
                    refine ⟨2335652337119614554083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24913624929275888576885 2335652337119614554083)
                    ·
                      rfl

theorem cell23_13646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_13646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13646 prefixEnd_13646 := by exact prefixLift 13646
  have htrace : WordTrace (prefixWord ++ tailWord_13646) baseStart_13646 baseEnd_13646 := by
    simpa [prefixWord, tailWord_13646, baseEnd_13646] using wordTrace_append hprefix tailTrace_13646
  have hstable : (prefixWord ++ tailWord_13646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13646).length < 2 ^ (prefixWord ++ tailWord_13646).sum := by decide
  have hdescent : baseEnd_13646 < baseStart_13646 := by decide
  rcases family_descends (prefixWord ++ tailWord_13646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13677 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_13677 : Nat := 118140960795 + 13677 * 2 ^ 59
def prefixEnd_13677 : Nat := 4983230072969 + 3 ^ 40 * 13677 * 2
def baseEnd_13677 : Nat := 7022874911648222374607

theorem tailTrace_13677 : CollatzResearch.WordTrace tailWord_13677 prefixEnd_13677 7022874911648222374607 := by
  unfold tailWord_13677
  simp only [CollatzResearch.WordTrace]
  refine ⟨498841171458039690743285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 332560780972026460495523 498841171458039690743285)
  ·
    refine ⟨46766359824191221007183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 498841171458039690743285 46766359824191221007183)
    ·
      refine ⟨70149539736286831510775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46766359824191221007183 70149539736286831510775)
      ·
        refine ⟨105224309604430247266163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70149539736286831510775 105224309604430247266163)
        ·
          refine ⟨157836464406645370899245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105224309604430247266163 157836464406645370899245)
          ·
            refine ⟨59188674152492014087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157836464406645370899245 59188674152492014087217)
            ·
              refine ⟨44391505614369010565413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59188674152492014087217 44391505614369010565413)
              ·
                refine ⟨8323407302694189481015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44391505614369010565413 8323407302694189481015)
                ·
                  refine ⟨12485110954041284221523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323407302694189481015 12485110954041284221523)
                  ·
                    refine ⟨18727666431061926332285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12485110954041284221523 18727666431061926332285)
                    ·
                      refine ⟨7022874911648222374607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18727666431061926332285 7022874911648222374607)
                      ·
                        rfl

theorem cell23_13677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_13677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13677 prefixEnd_13677 := by exact prefixLift 13677
  have htrace : WordTrace (prefixWord ++ tailWord_13677) baseStart_13677 baseEnd_13677 := by
    simpa [prefixWord, tailWord_13677, baseEnd_13677] using wordTrace_append hprefix tailTrace_13677
  have hstable : (prefixWord ++ tailWord_13677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13677).length < 2 ^ (prefixWord ++ tailWord_13677).sum := by decide
  have hdescent : baseEnd_13677 < baseStart_13677 := by decide
  rcases family_descends (prefixWord ++ tailWord_13677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13700 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_13700 : Nat := 118140960795 + 13700 * 2 ^ 59
def prefixEnd_13700 : Nat := 4983230072969 + 3 ^ 40 * 13700 * 2
def baseEnd_13700 : Nat := 7034684966701632387001

theorem tailTrace_13700 : CollatzResearch.WordTrace tailWord_13700 prefixEnd_13700 7034684966701632387001 := by
  unfold tailWord_13700
  simp only [CollatzResearch.WordTrace]
  refine ⟨249840025187357309415277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 333120033583143079220369 249840025187357309415277)
  ·
    refine ⟨93690009445258991030729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249840025187357309415277 93690009445258991030729)
    ·
      refine ⟨70267507083944243273047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93690009445258991030729 70267507083944243273047)
      ·
        refine ⟨105401260625916364909571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70267507083944243273047 105401260625916364909571)
        ·
          refine ⟨158101890938874547364357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105401260625916364909571 158101890938874547364357)
          ·
            refine ⟨29644104551038977630817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158101890938874547364357 29644104551038977630817)
            ·
              refine ⟨22233078413279233223113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29644104551038977630817 22233078413279233223113)
              ·
                refine ⟨16674808809959424917335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22233078413279233223113 16674808809959424917335)
                ·
                  refine ⟨25012213214939137376003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16674808809959424917335 25012213214939137376003)
                  ·
                    refine ⟨37518319822408706064005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25012213214939137376003 37518319822408706064005)
                    ·
                      refine ⟨7034684966701632387001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 37518319822408706064005 7034684966701632387001)
                      ·
                        rfl

theorem cell23_13700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_13700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13700 prefixEnd_13700 := by exact prefixLift 13700
  have htrace : WordTrace (prefixWord ++ tailWord_13700) baseStart_13700 baseEnd_13700 := by
    simpa [prefixWord, tailWord_13700, baseEnd_13700] using wordTrace_append hprefix tailTrace_13700
  have hstable : (prefixWord ++ tailWord_13700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13700).length < 2 ^ (prefixWord ++ tailWord_13700).sum := by decide
  have hdescent : baseEnd_13700 < baseStart_13700 := by decide
  rcases family_descends (prefixWord ++ tailWord_13700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13720 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_13720 : Nat := 118140960795 + 13720 * 2 ^ 59
def prefixEnd_13720 : Nat := 4983230072969 + 3 ^ 40 * 13720 * 2
def baseEnd_13720 : Nat := 7044954579791554136909

theorem tailTrace_13720 : CollatzResearch.WordTrace tailWord_13720 prefixEnd_13720 7044954579791554136909 := by
  unfold tailWord_13720
  simp only [CollatzResearch.WordTrace]
  refine ⟨250204755151129017279307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 333606340201505356372409 250204755151129017279307)
  ·
    refine ⟨375307132726693525918961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250204755151129017279307 375307132726693525918961)
    ·
      refine ⟨281480349545020144439221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375307132726693525918961 281480349545020144439221)
      ·
        refine ⟨26388782769845638541177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 281480349545020144439221 26388782769845638541177)
        ·
          refine ⟨19791587077384228905883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26388782769845638541177 19791587077384228905883)
          ·
            refine ⟨29687380616076343358825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19791587077384228905883 29687380616076343358825)
            ·
              refine ⟨22265535462057257519119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29687380616076343358825 22265535462057257519119)
              ·
                refine ⟨33398303193085886278679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22265535462057257519119 33398303193085886278679)
                ·
                  refine ⟨50097454789628829418019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33398303193085886278679 50097454789628829418019)
                  ·
                    refine ⟨75146182184443244127029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50097454789628829418019 75146182184443244127029)
                    ·
                      refine ⟨7044954579791554136909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 75146182184443244127029 7044954579791554136909)
                      ·
                        rfl

theorem cell23_13720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_13720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13720 prefixEnd_13720 := by exact prefixLift 13720
  have htrace : WordTrace (prefixWord ++ tailWord_13720) baseStart_13720 baseEnd_13720 := by
    simpa [prefixWord, tailWord_13720, baseEnd_13720] using wordTrace_append hprefix tailTrace_13720
  have hstable : (prefixWord ++ tailWord_13720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13720).length < 2 ^ (prefixWord ++ tailWord_13720).sum := by decide
  have hdescent : baseEnd_13720 < baseStart_13720 := by decide
  rcases family_descends (prefixWord ++ tailWord_13720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13746 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_13746 : Nat := 118140960795 + 13746 * 2 ^ 59
def prefixEnd_13746 : Nat := 4983230072969 + 3 ^ 40 * 13746 * 2
def baseEnd_13746 : Nat := 7058305076808452411789

theorem tailTrace_13746 : CollatzResearch.WordTrace tailWord_13746 prefixEnd_13746 7058305076808452411789 := by
  unfold tailWord_13746
  simp only [CollatzResearch.WordTrace]
  refine ⟨125339452052016118751273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 334238538805376316670061 125339452052016118751273)
  ·
    refine ⟨94004589039012089063455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125339452052016118751273 94004589039012089063455)
    ·
      refine ⟨141006883558518133595183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94004589039012089063455 141006883558518133595183)
      ·
        refine ⟨211510325337777200392775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141006883558518133595183 211510325337777200392775)
        ·
          refine ⟨317265488006665800589163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211510325337777200392775 317265488006665800589163)
          ·
            refine ⟨475898232009998700883745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317265488006665800589163 475898232009998700883745)
            ·
              refine ⟨356923674007499025662809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475898232009998700883745 356923674007499025662809)
              ·
                refine ⟨267692755505624269247107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356923674007499025662809 267692755505624269247107)
                ·
                  refine ⟨401539133258436403870661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267692755505624269247107 401539133258436403870661)
                  ·
                    refine ⟨75288587485956825725749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 401539133258436403870661 75288587485956825725749)
                    ·
                      refine ⟨7058305076808452411789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 75288587485956825725749 7058305076808452411789)
                      ·
                        rfl

theorem cell23_13746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_13746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13746 prefixEnd_13746 := by exact prefixLift 13746
  have htrace : WordTrace (prefixWord ++ tailWord_13746) baseStart_13746 baseEnd_13746 := by
    simpa [prefixWord, tailWord_13746, baseEnd_13746] using wordTrace_append hprefix tailTrace_13746
  have hstable : (prefixWord ++ tailWord_13746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13746).length < 2 ^ (prefixWord ++ tailWord_13746).sum := by decide
  have hdescent : baseEnd_13746 < baseStart_13746 := by decide
  rcases family_descends (prefixWord ++ tailWord_13746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13793 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_13793 : Nat := 118140960795 + 13793 * 2 ^ 59
def prefixEnd_13793 : Nat := 4983230072969 + 3 ^ 40 * 13793 * 2
def baseEnd_13793 : Nat := 7082438667569768524073

theorem tailTrace_13793 : CollatzResearch.WordTrace tailWord_13793 prefixEnd_13793 7082438667569768524073 := by
  unfold tailWord_13793
  simp only [CollatzResearch.WordTrace]
  refine ⟨503072039037791501966033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 335381359358527667977355 503072039037791501966033)
  ·
    refine ⟨377304029278343626474525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 503072039037791501966033 377304029278343626474525)
    ·
      refine ⟨141489010979378859927947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 377304029278343626474525 141489010979378859927947)
      ·
        refine ⟨212233516469068289891921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141489010979378859927947 212233516469068289891921)
        ·
          refine ⟨159175137351801217418941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212233516469068289891921 159175137351801217418941)
          ·
            refine ⟨59690676506925456532103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159175137351801217418941 59690676506925456532103)
            ·
              refine ⟨89536014760388184798155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59690676506925456532103 89536014760388184798155)
              ·
                refine ⟨134304022140582277197233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89536014760388184798155 134304022140582277197233)
                ·
                  refine ⟨100728016605436707897925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134304022140582277197233 100728016605436707897925)
                  ·
                    refine ⟨18886503113519382730861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 100728016605436707897925 18886503113519382730861)
                    ·
                      refine ⟨7082438667569768524073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 18886503113519382730861 7082438667569768524073)
                      ·
                        rfl

theorem cell23_13793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_13793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13793 prefixEnd_13793 := by exact prefixLift 13793
  have htrace : WordTrace (prefixWord ++ tailWord_13793) baseStart_13793 baseEnd_13793 := by
    simpa [prefixWord, tailWord_13793, baseEnd_13793] using wordTrace_append hprefix tailTrace_13793
  have hstable : (prefixWord ++ tailWord_13793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13793).length < 2 ^ (prefixWord ++ tailWord_13793).sum := by decide
  have hdescent : baseEnd_13793 < baseStart_13793 := by decide
  rcases family_descends (prefixWord ++ tailWord_13793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13796 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 11]
def baseStart_13796 : Nat := 118140960795 + 13796 * 2 ^ 59
def prefixEnd_13796 : Nat := 4983230072969 + 3 ^ 40 * 13796 * 2
def baseEnd_13796 : Nat := 787108789948139642951

theorem tailTrace_13796 : CollatzResearch.WordTrace tailWord_13796 prefixEnd_13796 787108789948139642951 := by
  unfold tailWord_13796
  simp only [CollatzResearch.WordTrace]
  refine ⟨251590729013461507162621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 335454305351282009550161 251590729013461507162621)
  ·
    refine ⟨94346523380048065185983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251590729013461507162621 94346523380048065185983)
    ·
      refine ⟨141519785070072097778975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94346523380048065185983 141519785070072097778975)
      ·
        refine ⟨212279677605108146668463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141519785070072097778975 212279677605108146668463)
        ·
          refine ⟨318419516407662220002695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212279677605108146668463 318419516407662220002695)
          ·
            refine ⟨477629274611493330004043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318419516407662220002695 477629274611493330004043)
            ·
              refine ⟨716443911917239995006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477629274611493330004043 716443911917239995006065)
              ·
                refine ⟨537332933937929996254549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716443911917239995006065 537332933937929996254549)
                ·
                  refine ⟨787108789948139642951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 537332933937929996254549 787108789948139642951)
                  ·
                    rfl

theorem cell23_13796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_13796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13796 prefixEnd_13796 := by exact prefixLift 13796
  have htrace : WordTrace (prefixWord ++ tailWord_13796) baseStart_13796 baseEnd_13796 := by
    simpa [prefixWord, tailWord_13796, baseEnd_13796] using wordTrace_append hprefix tailTrace_13796
  have hstable : (prefixWord ++ tailWord_13796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13796).length < 2 ^ (prefixWord ++ tailWord_13796).sum := by decide
  have hdescent : baseEnd_13796 < baseStart_13796 := by decide
  rcases family_descends (prefixWord ++ tailWord_13796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13807 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 2, 2, 2]
def baseStart_13807 : Nat := 118140960795 + 13807 * 2 ^ 59
def prefixEnd_13807 : Nat := 4983230072969 + 3 ^ 40 * 13807 * 2
def baseEnd_13807 : Nat := 7089627396732713749009

theorem tailTrace_13807 : CollatzResearch.WordTrace tailWord_13807 prefixEnd_13807 7089627396732713749009 := by
  unfold tailWord_13807
  simp only [CollatzResearch.WordTrace]
  refine ⟨503582660987071892975675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 335721773991381261983783 503582660987071892975675)
  ·
    refine ⟨755373991480607839463513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503582660987071892975675 755373991480607839463513)
    ·
      refine ⟨566530493610455879597635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755373991480607839463513 566530493610455879597635)
      ·
        refine ⟨849795740415683819396453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566530493610455879597635 849795740415683819396453)
        ·
          refine ⟨159336701327940716136835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 849795740415683819396453 159336701327940716136835)
          ·
            refine ⟨239005051991911074205253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159336701327940716136835 239005051991911074205253)
            ·
              refine ⟨44813447248483326413485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239005051991911074205253 44813447248483326413485)
              ·
                refine ⟨16805042718181247405057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44813447248483326413485 16805042718181247405057)
                ·
                  refine ⟨12603782038635935553793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16805042718181247405057 12603782038635935553793)
                  ·
                    refine ⟨9452836528976951665345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12603782038635935553793 9452836528976951665345)
                    ·
                      refine ⟨7089627396732713749009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9452836528976951665345 7089627396732713749009)
                      ·
                        rfl

theorem cell23_13807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2, 2].length) (baseStart_13807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13807 prefixEnd_13807 := by exact prefixLift 13807
  have htrace : WordTrace (prefixWord ++ tailWord_13807) baseStart_13807 baseEnd_13807 := by
    simpa [prefixWord, tailWord_13807, baseEnd_13807] using wordTrace_append hprefix tailTrace_13807
  have hstable : (prefixWord ++ tailWord_13807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13807).length < 2 ^ (prefixWord ++ tailWord_13807).sum := by decide
  have hdescent : baseEnd_13807 < baseStart_13807 := by decide
  rcases family_descends (prefixWord ++ tailWord_13807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13828 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_13828 : Nat := 118140960795 + 13828 * 2 ^ 59
def prefixEnd_13828 : Nat := 4983230072969 + 3 ^ 40 * 13828 * 2
def baseEnd_13828 : Nat := 7100410490477131586413

theorem tailTrace_13828 : CollatzResearch.WordTrace tailWord_13828 prefixEnd_13828 7100410490477131586413 := by
  unfold tailWord_13828
  simp only [CollatzResearch.WordTrace]
  refine ⟨252174296955496239745069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 336232395940661652993425 252174296955496239745069)
  ·
    refine ⟨94565361358311089904401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252174296955496239745069 94565361358311089904401)
    ·
      refine ⟨70924021018733317428301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94565361358311089904401 70924021018733317428301)
      ·
        refine ⟨26596507882024994035613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70924021018733317428301 26596507882024994035613)
        ·
          refine ⟨9973690455759372763355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26596507882024994035613 9973690455759372763355)
          ·
            refine ⟨14960535683639059145033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9973690455759372763355 14960535683639059145033)
            ·
              refine ⟨11220401762729294358775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14960535683639059145033 11220401762729294358775)
              ·
                refine ⟨16830602644093941538163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11220401762729294358775 16830602644093941538163)
                ·
                  refine ⟨25245903966140912307245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16830602644093941538163 25245903966140912307245)
                  ·
                    refine ⟨9467213987302842115217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25245903966140912307245 9467213987302842115217)
                    ·
                      refine ⟨7100410490477131586413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9467213987302842115217 7100410490477131586413)
                      ·
                        rfl

theorem cell23_13828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_13828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13828 prefixEnd_13828 := by exact prefixLift 13828
  have htrace : WordTrace (prefixWord ++ tailWord_13828) baseStart_13828 baseEnd_13828 := by
    simpa [prefixWord, tailWord_13828, baseEnd_13828] using wordTrace_append hprefix tailTrace_13828
  have hstable : (prefixWord ++ tailWord_13828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13828).length < 2 ^ (prefixWord ++ tailWord_13828).sum := by decide
  have hdescent : baseEnd_13828 < baseStart_13828 := by decide
  rcases family_descends (prefixWord ++ tailWord_13828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13853 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_13853 : Nat := 118140960795 + 13853 * 2 ^ 59
def prefixEnd_13853 : Nat := 4983230072969 + 3 ^ 40 * 13853 * 2
def baseEnd_13853 : Nat := 7113247506839533773797

theorem tailTrace_13853 : CollatzResearch.WordTrace tailWord_13853 prefixEnd_13853 7113247506839533773797 := by
  unfold tailWord_13853
  simp only [CollatzResearch.WordTrace]
  refine ⟨505260418820421749150213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 336840279213614499433475 505260418820421749150213)
  ·
    refine ⟨94736328528829077965665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 505260418820421749150213 94736328528829077965665)
    ·
      refine ⟨71052246396621808474249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94736328528829077965665 71052246396621808474249)
      ·
        refine ⟨53289184797466356355687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71052246396621808474249 53289184797466356355687)
        ·
          refine ⟨79933777196199534533531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53289184797466356355687 79933777196199534533531)
          ·
            refine ⟨119900665794299301800297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79933777196199534533531 119900665794299301800297)
            ·
              refine ⟨89925499345724476350223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119900665794299301800297 89925499345724476350223)
              ·
                refine ⟨134888249018586714525335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89925499345724476350223 134888249018586714525335)
                ·
                  refine ⟨202332373527880071788003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134888249018586714525335 202332373527880071788003)
                  ·
                    refine ⟨303498560291820107682005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 202332373527880071788003 303498560291820107682005)
                    ·
                      refine ⟨7113247506839533773797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 303498560291820107682005 7113247506839533773797)
                      ·
                        rfl

theorem cell23_13853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_13853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13853 prefixEnd_13853 := by exact prefixLift 13853
  have htrace : WordTrace (prefixWord ++ tailWord_13853) baseStart_13853 baseEnd_13853 := by
    simpa [prefixWord, tailWord_13853, baseEnd_13853] using wordTrace_append hprefix tailTrace_13853
  have hstable : (prefixWord ++ tailWord_13853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13853).length < 2 ^ (prefixWord ++ tailWord_13853).sum := by decide
  have hdescent : baseEnd_13853 < baseStart_13853 := by decide
  rcases family_descends (prefixWord ++ tailWord_13853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13894 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_13894 : Nat := 118140960795 + 13894 * 2 ^ 59
def prefixEnd_13894 : Nat := 4983230072969 + 3 ^ 40 * 13894 * 2
def baseEnd_13894 : Nat := 2378100071224624453703

theorem tailTrace_13894 : CollatzResearch.WordTrace tailWord_13894 prefixEnd_13894 2378100071224624453703 := by
  unfold tailWord_13894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836119114746429731023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 337837207781257167595157 15836119114746429731023)
  ·
    refine ⟨23754178672119644596535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15836119114746429731023 23754178672119644596535)
    ·
      refine ⟨35631268008179466894803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23754178672119644596535 35631268008179466894803)
      ·
        refine ⟨53446902012269200342205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35631268008179466894803 53446902012269200342205)
        ·
          refine ⟨20042588254600950128327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53446902012269200342205 20042588254600950128327)
          ·
            refine ⟨30063882381901425192491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20042588254600950128327 30063882381901425192491)
            ·
              refine ⟨45095823572852137788737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30063882381901425192491 45095823572852137788737)
              ·
                refine ⟨33821867679639103341553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45095823572852137788737 33821867679639103341553)
                ·
                  refine ⟨25366400759729327506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33821867679639103341553 25366400759729327506165)
                  ·
                    refine ⟨2378100071224624453703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25366400759729327506165 2378100071224624453703)
                    ·
                      rfl

theorem cell23_13894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_13894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13894 prefixEnd_13894 := by exact prefixLift 13894
  have htrace : WordTrace (prefixWord ++ tailWord_13894) baseStart_13894 baseEnd_13894 := by
    simpa [prefixWord, tailWord_13894, baseEnd_13894] using wordTrace_append hprefix tailTrace_13894
  have hstable : (prefixWord ++ tailWord_13894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13894).length < 2 ^ (prefixWord ++ tailWord_13894).sum := by decide
  have hdescent : baseEnd_13894 < baseStart_13894 := by decide
  rcases family_descends (prefixWord ++ tailWord_13894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13900 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_13900 : Nat := 118140960795 + 13900 * 2 ^ 59
def prefixEnd_13900 : Nat := 4983230072969 + 3 ^ 40 * 13900 * 2
def baseEnd_13900 : Nat := 7137381097600849886081

theorem tailTrace_13900 : CollatzResearch.WordTrace tailWord_13900 prefixEnd_13900 7137381097600849886081 := by
  unfold tailWord_13900
  simp only [CollatzResearch.WordTrace]
  refine ⟨253487324825074388055577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 337983099766765850740769 253487324825074388055577)
  ·
    refine ⟨190115493618805791041683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253487324825074388055577 190115493618805791041683)
    ·
      refine ⟨285173240428208686562525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190115493618805791041683 285173240428208686562525)
      ·
        refine ⟨106939965160578257460947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285173240428208686562525 106939965160578257460947)
        ·
          refine ⟨160409947740867386191421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106939965160578257460947 160409947740867386191421)
          ·
            refine ⟨60153730402825269821783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160409947740867386191421 60153730402825269821783)
            ·
              refine ⟨90230595604237904732675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60153730402825269821783 90230595604237904732675)
              ·
                refine ⟨135345893406356857099013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90230595604237904732675 135345893406356857099013)
                ·
                  refine ⟨25377355013691910706065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135345893406356857099013 25377355013691910706065)
                  ·
                    refine ⟨19033016260268933029549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25377355013691910706065 19033016260268933029549)
                    ·
                      refine ⟨7137381097600849886081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19033016260268933029549 7137381097600849886081)
                      ·
                        rfl

theorem cell23_13900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_13900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13900 prefixEnd_13900 := by exact prefixLift 13900
  have htrace : WordTrace (prefixWord ++ tailWord_13900) baseStart_13900 baseEnd_13900 := by
    simpa [prefixWord, tailWord_13900, baseEnd_13900] using wordTrace_append hprefix tailTrace_13900
  have hstable : (prefixWord ++ tailWord_13900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13900).length < 2 ^ (prefixWord ++ tailWord_13900).sum := by decide
  have hdescent : baseEnd_13900 < baseStart_13900 := by decide
  rcases family_descends (prefixWord ++ tailWord_13900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13903 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 6]
def baseStart_13903 : Nat := 118140960795 + 13903 * 2 ^ 59
def prefixEnd_13903 : Nat := 4983230072969 + 3 ^ 40 * 13903 * 2
def baseEnd_13903 : Nat := 793213504396037572063

theorem tailTrace_13903 : CollatzResearch.WordTrace tailWord_13903 prefixEnd_13903 793213504396037572063 := by
  unfold tailWord_13903
  simp only [CollatzResearch.WordTrace]
  refine ⟨507084068639280288470363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 338056045759520192313575 507084068639280288470363)
  ·
    refine ⟨760626102958920432705545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 507084068639280288470363 760626102958920432705545)
    ·
      refine ⟨570469577219190324529159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 760626102958920432705545 570469577219190324529159)
      ·
        refine ⟨855704365828785486793739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570469577219190324529159 855704365828785486793739)
        ·
          refine ⟨1283556548743178230190609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855704365828785486793739 1283556548743178230190609)
          ·
            refine ⟨962667411557383672642957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283556548743178230190609 962667411557383672642957)
            ·
              refine ⟨361000279334018877241109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 962667411557383672642957 361000279334018877241109)
              ·
                refine ⟨16921888093782134870677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 361000279334018877241109 16921888093782134870677)
                ·
                  refine ⟨793213504396037572063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16921888093782134870677 793213504396037572063)
                  ·
                    rfl

theorem cell23_13903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 6].length) (baseStart_13903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13903 prefixEnd_13903 := by exact prefixLift 13903
  have htrace : WordTrace (prefixWord ++ tailWord_13903) baseStart_13903 baseEnd_13903 := by
    simpa [prefixWord, tailWord_13903, baseEnd_13903] using wordTrace_append hprefix tailTrace_13903
  have hstable : (prefixWord ++ tailWord_13903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13903).length < 2 ^ (prefixWord ++ tailWord_13903).sum := by decide
  have hdescent : baseEnd_13903 < baseStart_13903 := by decide
  rcases family_descends (prefixWord ++ tailWord_13903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13934 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_13934 : Nat := 118140960795 + 13934 * 2 ^ 59
def prefixEnd_13934 : Nat := 4983230072969 + 3 ^ 40 * 13934 * 2
def baseEnd_13934 : Nat := 7154839439853716860925

theorem tailTrace_13934 : CollatzResearch.WordTrace tailWord_13934 prefixEnd_13934 7154839439853716860925 := by
  unfold tailWord_13934
  simp only [CollatzResearch.WordTrace]
  refine ⟨63526841440871572856107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 338809821017981721899237 63526841440871572856107)
  ·
    refine ⟨95290262161307359284161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63526841440871572856107 95290262161307359284161)
    ·
      refine ⟨71467696620980519463121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95290262161307359284161 71467696620980519463121)
      ·
        refine ⟨53600772465735389597341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71467696620980519463121 53600772465735389597341)
        ·
          refine ⟨20100289674650771099003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53600772465735389597341 20100289674650771099003)
          ·
            refine ⟨30150434511976156648505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20100289674650771099003 30150434511976156648505)
            ·
              refine ⟨22612825883982117486379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30150434511976156648505 22612825883982117486379)
              ·
                refine ⟨33919238825973176229569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22612825883982117486379 33919238825973176229569)
                ·
                  refine ⟨25439429119479882172177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33919238825973176229569 25439429119479882172177)
                  ·
                    refine ⟨19079571839609911629133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25439429119479882172177 19079571839609911629133)
                    ·
                      refine ⟨7154839439853716860925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19079571839609911629133 7154839439853716860925)
                      ·
                        rfl

theorem cell23_13934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_13934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13934 prefixEnd_13934 := by exact prefixLift 13934
  have htrace : WordTrace (prefixWord ++ tailWord_13934) baseStart_13934 baseEnd_13934 := by
    simpa [prefixWord, tailWord_13934, baseEnd_13934] using wordTrace_append hprefix tailTrace_13934
  have hstable : (prefixWord ++ tailWord_13934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13934).length < 2 ^ (prefixWord ++ tailWord_13934).sum := by decide
  have hdescent : baseEnd_13934 < baseStart_13934 := by decide
  rcases family_descends (prefixWord ++ tailWord_13934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13957 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_13957 : Nat := 118140960795 + 13957 * 2 ^ 59
def prefixEnd_13957 : Nat := 4983230072969 + 3 ^ 40 * 13957 * 2
def baseEnd_13957 : Nat := 7166649494907126873319

theorem tailTrace_13957 : CollatzResearch.WordTrace tailWord_13957 prefixEnd_13957 7166649494907126873319 := by
  unfold tailWord_13957
  simp only [CollatzResearch.WordTrace]
  refine ⟨509053610443647510936125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 339369073629098340624083 509053610443647510936125)
  ·
    refine ⟨190895103916367816601047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 509053610443647510936125 190895103916367816601047)
    ·
      refine ⟨286342655874551724901571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190895103916367816601047 286342655874551724901571)
      ·
        refine ⟨429513983811827587352357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286342655874551724901571 429513983811827587352357)
        ·
          refine ⟨80533871964717672628567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429513983811827587352357 80533871964717672628567)
          ·
            refine ⟨120800807947076508942851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80533871964717672628567 120800807947076508942851)
            ·
              refine ⟨181201211920614763414277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120800807947076508942851 181201211920614763414277)
              ·
                refine ⟨33975227235115268140177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181201211920614763414277 33975227235115268140177)
                ·
                  refine ⟨25481420426336451105133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33975227235115268140177 25481420426336451105133)
                  ·
                    refine ⟨9555532659876169164425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25481420426336451105133 9555532659876169164425)
                    ·
                      refine ⟨7166649494907126873319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9555532659876169164425 7166649494907126873319)
                      ·
                        rfl

theorem cell23_13957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_13957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13957 prefixEnd_13957 := by exact prefixLift 13957
  have htrace : WordTrace (prefixWord ++ tailWord_13957) baseStart_13957 baseEnd_13957 := by
    simpa [prefixWord, tailWord_13957, baseEnd_13957] using wordTrace_append hprefix tailTrace_13957
  have hstable : (prefixWord ++ tailWord_13957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13957).length < 2 ^ (prefixWord ++ tailWord_13957).sum := by decide
  have hdescent : baseEnd_13957 < baseStart_13957 := by decide
  rcases family_descends (prefixWord ++ tailWord_13957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13963 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 6]
def baseStart_13963 : Nat := 118140960795 + 13963 * 2 ^ 59
def prefixEnd_13963 : Nat := 4983230072969 + 3 ^ 40 * 13963 * 2
def baseEnd_13963 : Nat := 2389910126278034466097

theorem tailTrace_13963 : CollatzResearch.WordTrace tailWord_13963 prefixEnd_13963 2389910126278034466097 := by
  unfold tailWord_13963
  simp only [CollatzResearch.WordTrace]
  refine ⟨509272448421910535654543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 339514965614607023769695 509272448421910535654543)
  ·
    refine ⟨763908672632865803481815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509272448421910535654543 763908672632865803481815)
    ·
      refine ⟨1145863008949298705222723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763908672632865803481815 1145863008949298705222723)
      ·
        refine ⟨1718794513423948057834085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145863008949298705222723 1718794513423948057834085)
        ·
          refine ⟨322273971266990260843891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1718794513423948057834085 322273971266990260843891)
          ·
            refine ⟨483410956900485391265837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322273971266990260843891 483410956900485391265837)
            ·
              refine ⟨181279108837682021724689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483410956900485391265837 181279108837682021724689)
              ·
                refine ⟨135959331628261516293517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181279108837682021724689 135959331628261516293517)
                ·
                  refine ⟨50984749360598068610069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135959331628261516293517 50984749360598068610069)
                  ·
                    refine ⟨2389910126278034466097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 50984749360598068610069 2389910126278034466097)
                    ·
                      rfl

theorem cell23_13963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_13963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13963 prefixEnd_13963 := by exact prefixLift 13963
  have htrace : WordTrace (prefixWord ++ tailWord_13963) baseStart_13963 baseEnd_13963 := by
    simpa [prefixWord, tailWord_13963, baseEnd_13963] using wordTrace_append hprefix tailTrace_13963
  have hstable : (prefixWord ++ tailWord_13963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13963).length < 2 ^ (prefixWord ++ tailWord_13963).sum := by decide
  have hdescent : baseEnd_13963 < baseStart_13963 := by decide
  rcases family_descends (prefixWord ++ tailWord_13963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13964 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_13964 : Nat := 118140960795 + 13964 * 2 ^ 59
def prefixEnd_13964 : Nat := 4983230072969 + 3 ^ 40 * 13964 * 2
def baseEnd_13964 : Nat := 7170243859488599485787

theorem tailTrace_13964 : CollatzResearch.WordTrace tailWord_13964 prefixEnd_13964 7170243859488599485787 := by
  unfold tailWord_13964
  simp only [CollatzResearch.WordTrace]
  refine ⟨254654460709143853220473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 339539280945525137627297 254654460709143853220473)
  ·
    refine ⟨190990845531857889915355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254654460709143853220473 190990845531857889915355)
    ·
      refine ⟨286486268297786834873033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190990845531857889915355 286486268297786834873033)
      ·
        refine ⟨214864701223340126154775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286486268297786834873033 214864701223340126154775)
        ·
          refine ⟨322297051835010189232163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214864701223340126154775 322297051835010189232163)
          ·
            refine ⟨483445577752515283848245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322297051835010189232163 483445577752515283848245)
            ·
              refine ⟨45323022914298307860773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 483445577752515283848245 45323022914298307860773)
              ·
                refine ⟨8498066796430932723895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45323022914298307860773 8498066796430932723895)
                ·
                  refine ⟨12747100194646399085843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8498066796430932723895 12747100194646399085843)
                  ·
                    refine ⟨19120650291969598628765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12747100194646399085843 19120650291969598628765)
                    ·
                      refine ⟨7170243859488599485787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19120650291969598628765 7170243859488599485787)
                      ·
                        rfl

theorem cell23_13964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_13964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13964 prefixEnd_13964 := by exact prefixLift 13964
  have htrace : WordTrace (prefixWord ++ tailWord_13964) baseStart_13964 baseEnd_13964 := by
    simpa [prefixWord, tailWord_13964, baseEnd_13964] using wordTrace_append hprefix tailTrace_13964
  have hstable : (prefixWord ++ tailWord_13964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13964).length < 2 ^ (prefixWord ++ tailWord_13964).sum := by decide
  have hdescent : baseEnd_13964 < baseStart_13964 := by decide
  rcases family_descends (prefixWord ++ tailWord_13964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13997 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_13997 : Nat := 118140960795 + 13997 * 2 ^ 59
def prefixEnd_13997 : Nat := 4983230072969 + 3 ^ 40 * 13997 * 2
def baseEnd_13997 : Nat := 2395729573695656791045

theorem tailTrace_13997 : CollatzResearch.WordTrace tailWord_13997 prefixEnd_13997 2395729573695656791045 := by
  unfold tailWord_13997
  simp only [CollatzResearch.WordTrace]
  refine ⟨510512530298734342392245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 340341686865822894928163 510512530298734342392245)
  ·
    refine ⟨47860549715506344599273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 510512530298734342392245 47860549715506344599273)
    ·
      refine ⟨35895412286629758449455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47860549715506344599273 35895412286629758449455)
      ·
        refine ⟨53843118429944637674183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35895412286629758449455 53843118429944637674183)
        ·
          refine ⟨80764677644916956511275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53843118429944637674183 80764677644916956511275)
          ·
            refine ⟨121147016467375434766913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80764677644916956511275 121147016467375434766913)
            ·
              refine ⟨90860262350531576075185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121147016467375434766913 90860262350531576075185)
              ·
                refine ⟨68145196762898682056389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90860262350531576075185 68145196762898682056389)
                ·
                  refine ⟨12777224393043502885573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68145196762898682056389 12777224393043502885573)
                  ·
                    refine ⟨2395729573695656791045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12777224393043502885573 2395729573695656791045)
                    ·
                      rfl

theorem cell23_13997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_13997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_13997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_13997 prefixEnd_13997 := by exact prefixLift 13997
  have htrace : WordTrace (prefixWord ++ tailWord_13997) baseStart_13997 baseEnd_13997 := by
    simpa [prefixWord, tailWord_13997, baseEnd_13997] using wordTrace_append hprefix tailTrace_13997
  have hstable : (prefixWord ++ tailWord_13997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13997).length < 2 ^ (prefixWord ++ tailWord_13997).sum := by decide
  have hdescent : baseEnd_13997 < baseStart_13997 := by decide
  rcases family_descends (prefixWord ++ tailWord_13997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14000 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_14000 : Nat := 118140960795 + 14000 * 2 ^ 59
def prefixEnd_14000 : Nat := 4983230072969 + 3 ^ 40 * 14000 * 2
def baseEnd_14000 : Nat := 7188729163050458635621

theorem tailTrace_14000 : CollatzResearch.WordTrace tailWord_14000 prefixEnd_14000 7188729163050458635621 := by
  unfold tailWord_14000
  simp only [CollatzResearch.WordTrace]
  refine ⟨255310974643932927375727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 340414632858577236500969 255310974643932927375727)
  ·
    refine ⟨382966461965899391063591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255310974643932927375727 382966461965899391063591)
    ·
      refine ⟨574449692948849086595387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382966461965899391063591 574449692948849086595387)
      ·
        refine ⟨861674539423273629893081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574449692948849086595387 861674539423273629893081)
        ·
          refine ⟨646255904567455222419811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861674539423273629893081 646255904567455222419811)
          ·
            refine ⟨969383856851182833629717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646255904567455222419811 969383856851182833629717)
            ·
              refine ⟨45439868289899195326393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 969383856851182833629717 45439868289899195326393)
              ·
                refine ⟨34079901217424396494795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45439868289899195326393 34079901217424396494795)
                ·
                  refine ⟨51119851826136594742193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34079901217424396494795 51119851826136594742193)
                  ·
                    refine ⟨38339888869602446056645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51119851826136594742193 38339888869602446056645)
                    ·
                      refine ⟨7188729163050458635621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 38339888869602446056645 7188729163050458635621)
                      ·
                        rfl

theorem cell23_14000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_14000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14000 prefixEnd_14000 := by exact prefixLift 14000
  have htrace : WordTrace (prefixWord ++ tailWord_14000) baseStart_14000 baseEnd_14000 := by
    simpa [prefixWord, tailWord_14000, baseEnd_14000] using wordTrace_append hprefix tailTrace_14000
  have hstable : (prefixWord ++ tailWord_14000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14000).length < 2 ^ (prefixWord ++ tailWord_14000).sum := by decide
  have hdescent : baseEnd_14000 < baseStart_14000 := by decide
  rcases family_descends (prefixWord ++ tailWord_14000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14014 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_14014 : Nat := 118140960795 + 14014 * 2 ^ 59
def prefixEnd_14014 : Nat := 4983230072969 + 3 ^ 40 * 14014 * 2
def baseEnd_14014 : Nat := 2398639297404467953519

theorem tailTrace_14014 : CollatzResearch.WordTrace tailWord_14014 prefixEnd_14014 2398639297404467953519 := by
  unfold tailWord_14014
  simp only [CollatzResearch.WordTrace]
  refine ⟨63891571404643280720137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 340755047491430830507397 63891571404643280720137)
  ·
    refine ⟨47918678553482460540103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63891571404643280720137 47918678553482460540103)
    ·
      refine ⟨71878017830223690810155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47918678553482460540103 71878017830223690810155)
      ·
        refine ⟨107817026745335536215233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71878017830223690810155 107817026745335536215233)
        ·
          refine ⟨80862770059001652161425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107817026745335536215233 80862770059001652161425)
          ·
            refine ⟨60647077544251239121069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80862770059001652161425 60647077544251239121069)
            ·
              refine ⟨22742654079094214670401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60647077544251239121069 22742654079094214670401)
              ·
                refine ⟨17056990559320661002801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22742654079094214670401 17056990559320661002801)
                ·
                  refine ⟨12792742919490495752101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056990559320661002801 12792742919490495752101)
                  ·
                    refine ⟨2398639297404467953519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12792742919490495752101 2398639297404467953519)
                    ·
                      rfl

theorem cell23_14014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_14014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14014 prefixEnd_14014 := by exact prefixLift 14014
  have htrace : WordTrace (prefixWord ++ tailWord_14014) baseStart_14014 baseEnd_14014 := by
    simpa [prefixWord, tailWord_14014, baseEnd_14014] using wordTrace_append hprefix tailTrace_14014
  have hstable : (prefixWord ++ tailWord_14014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14014).length < 2 ^ (prefixWord ++ tailWord_14014).sum := by decide
  have hdescent : baseEnd_14014 < baseStart_14014 := by decide
  rcases family_descends (prefixWord ++ tailWord_14014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14034 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_14034 : Nat := 118140960795 + 14034 * 2 ^ 59
def prefixEnd_14034 : Nat := 4983230072969 + 3 ^ 40 * 14034 * 2
def baseEnd_14034 : Nat := 7206187505303325610465

theorem tailTrace_14034 : CollatzResearch.WordTrace tailWord_14034 prefixEnd_14034 7206187505303325610465 := by
  unfold tailWord_14034
  simp only [CollatzResearch.WordTrace]
  refine ⟨127965507791172415372289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 341241354109793107659437 127965507791172415372289)
  ·
    refine ⟨95974130843379311529217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127965507791172415372289 95974130843379311529217)
    ·
      refine ⟨71980598132534483646913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95974130843379311529217 71980598132534483646913)
      ·
        refine ⟨53985448599400862735185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71980598132534483646913 53985448599400862735185)
        ·
          refine ⟨40489086449550647051389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53985448599400862735185 40489086449550647051389)
          ·
            refine ⟨15183407418581492644271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40489086449550647051389 15183407418581492644271)
            ·
              refine ⟨22775111127872238966407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15183407418581492644271 22775111127872238966407)
              ·
                refine ⟨34162666691808358449611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22775111127872238966407 34162666691808358449611)
                ·
                  refine ⟨51244000037712537674417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34162666691808358449611 51244000037712537674417)
                  ·
                    refine ⟨38433000028284403255813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51244000037712537674417 38433000028284403255813)
                    ·
                      refine ⟨7206187505303325610465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 38433000028284403255813 7206187505303325610465)
                      ·
                        rfl

theorem cell23_14034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_14034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14034 prefixEnd_14034 := by exact prefixLift 14034
  have htrace : WordTrace (prefixWord ++ tailWord_14034) baseStart_14034 baseEnd_14034 := by
    simpa [prefixWord, tailWord_14034, baseEnd_14034] using wordTrace_append hprefix tailTrace_14034
  have hstable : (prefixWord ++ tailWord_14034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14034).length < 2 ^ (prefixWord ++ tailWord_14034).sum := by decide
  have hdescent : baseEnd_14034 < baseStart_14034 := by decide
  rcases family_descends (prefixWord ++ tailWord_14034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14038 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_14038 : Nat := 118140960795 + 14038 * 2 ^ 59
def prefixEnd_14038 : Nat := 4983230072969 + 3 ^ 40 * 14038 * 2
def baseEnd_14038 : Nat := 7208241427921309960447

theorem tailTrace_14038 : CollatzResearch.WordTrace tailWord_14038 prefixEnd_14038 7208241427921309960447 := by
  unfold tailWord_14038
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000495196887396539673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 341338615433465563089845 32000495196887396539673)
  ·
    refine ⟨24000371397665547404755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32000495196887396539673 24000371397665547404755)
    ·
      refine ⟨36000557096498321107133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24000371397665547404755 36000557096498321107133)
      ·
        refine ⟨13500208911186870415175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36000557096498321107133 13500208911186870415175)
        ·
          refine ⟨20250313366780305622763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13500208911186870415175 20250313366780305622763)
          ·
            refine ⟨30375470050170458434145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250313366780305622763 30375470050170458434145)
            ·
              refine ⟨22781602537627843825609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30375470050170458434145 22781602537627843825609)
              ·
                refine ⟨17086201903220882869207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22781602537627843825609 17086201903220882869207)
                ·
                  refine ⟨25629302854831324303811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17086201903220882869207 25629302854831324303811)
                  ·
                    refine ⟨38443954282246986455717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25629302854831324303811 38443954282246986455717)
                    ·
                      refine ⟨7208241427921309960447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 38443954282246986455717 7208241427921309960447)
                      ·
                        rfl

theorem cell23_14038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_14038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14038 prefixEnd_14038 := by exact prefixLift 14038
  have htrace : WordTrace (prefixWord ++ tailWord_14038) baseStart_14038 baseEnd_14038 := by
    simpa [prefixWord, tailWord_14038, baseEnd_14038] using wordTrace_append hprefix tailTrace_14038
  have hstable : (prefixWord ++ tailWord_14038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14038).length < 2 ^ (prefixWord ++ tailWord_14038).sum := by decide
  have hdescent : baseEnd_14038 < baseStart_14038 := by decide
  rcases family_descends (prefixWord ++ tailWord_14038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14077 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_14077 : Nat := 118140960795 + 14077 * 2 ^ 59
def prefixEnd_14077 : Nat := 4983230072969 + 3 ^ 40 * 14077 * 2
def baseEnd_14077 : Nat := 7228267173446657372767

theorem tailTrace_14077 : CollatzResearch.WordTrace tailWord_14077 prefixEnd_14077 7228267173446657372767 := by
  unfold tailWord_14077
  simp only [CollatzResearch.WordTrace]
  refine ⟨513430370008908005304485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 342286913339272003536323 513430370008908005304485)
  ·
    refine ⟨96268194376670250994591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 513430370008908005304485 96268194376670250994591)
    ·
      refine ⟨144402291565005376491887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96268194376670250994591 144402291565005376491887)
      ·
        refine ⟨216603437347508064737831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144402291565005376491887 216603437347508064737831)
        ·
          refine ⟨324905156021262097106747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216603437347508064737831 324905156021262097106747)
          ·
            refine ⟨487357734031893145660121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324905156021262097106747 487357734031893145660121)
            ·
              refine ⟨365518300523919859245091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487357734031893145660121 365518300523919859245091)
              ·
                refine ⟨548277450785879788867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365518300523919859245091 548277450785879788867637)
                ·
                  refine ⟨51401011011176230206341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 548277450785879788867637 51401011011176230206341)
                  ·
                    refine ⟨9637689564595543163689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51401011011176230206341 9637689564595543163689)
                    ·
                      refine ⟨7228267173446657372767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9637689564595543163689 7228267173446657372767)
                      ·
                        rfl

theorem cell23_14077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_14077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14077 prefixEnd_14077 := by exact prefixLift 14077
  have htrace : WordTrace (prefixWord ++ tailWord_14077) baseStart_14077 baseEnd_14077 := by
    simpa [prefixWord, tailWord_14077, baseEnd_14077] using wordTrace_append hprefix tailTrace_14077
  have hstable : (prefixWord ++ tailWord_14077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14077).length < 2 ^ (prefixWord ++ tailWord_14077).sum := by decide
  have hdescent : baseEnd_14077 < baseStart_14077 := by decide
  rcases family_descends (prefixWord ++ tailWord_14077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14080 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_14080 : Nat := 118140960795 + 14080 * 2 ^ 59
def prefixEnd_14080 : Nat := 4983230072969 + 3 ^ 40 * 14080 * 2
def baseEnd_14080 : Nat := 7229807615410145635253

theorem tailTrace_14080 : CollatzResearch.WordTrace tailWord_14080 prefixEnd_14080 7229807615410145635253 := by
  unfold tailWord_14080
  simp only [CollatzResearch.WordTrace]
  refine ⟨256769894499019758831847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 342359859332026345109129 256769894499019758831847)
  ·
    refine ⟨385154841748529638247771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256769894499019758831847 385154841748529638247771)
    ·
      refine ⟨577732262622794457371657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385154841748529638247771 577732262622794457371657)
      ·
        refine ⟨433299196967095843028743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577732262622794457371657 433299196967095843028743)
        ·
          refine ⟨649948795450643764543115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433299196967095843028743 649948795450643764543115)
          ·
            refine ⟨974923193175965646814673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649948795450643764543115 974923193175965646814673)
            ·
              refine ⟨731192394881974235111005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974923193175965646814673 731192394881974235111005)
              ·
                refine ⟨274197148080740338166627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731192394881974235111005 274197148080740338166627)
                ·
                  refine ⟨411295722121110507249941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274197148080740338166627 411295722121110507249941)
                  ·
                    refine ⟨19279486974427055027341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 411295722121110507249941 19279486974427055027341)
                    ·
                      refine ⟨7229807615410145635253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19279486974427055027341 7229807615410145635253)
                      ·
                        rfl

theorem cell23_14080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_14080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14080 prefixEnd_14080 := by exact prefixLift 14080
  have htrace : WordTrace (prefixWord ++ tailWord_14080) baseStart_14080 baseEnd_14080 := by
    simpa [prefixWord, tailWord_14080, baseEnd_14080] using wordTrace_append hprefix tailTrace_14080
  have hstable : (prefixWord ++ tailWord_14080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14080).length < 2 ^ (prefixWord ++ tailWord_14080).sum := by decide
  have hdescent : baseEnd_14080 < baseStart_14080 := by decide
  rcases family_descends (prefixWord ++ tailWord_14080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14098 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_14098 : Nat := 118140960795 + 14098 * 2 ^ 59
def prefixEnd_14098 : Nat := 4983230072969 + 3 ^ 40 * 14098 * 2
def baseEnd_14098 : Nat := 7239050267191075210171

theorem tailTrace_14098 : CollatzResearch.WordTrace tailWord_14098 prefixEnd_14098 7239050267191075210171 := by
  unfold tailWord_14098
  simp only [CollatzResearch.WordTrace]
  refine ⟨128549075733207147954737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 342797535288552394545965 128549075733207147954737)
  ·
    refine ⟨96411806799905360966053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128549075733207147954737 96411806799905360966053)
    ·
      refine ⟨18077213774982255181135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96411806799905360966053 18077213774982255181135)
      ·
        refine ⟨27115820662473382771703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18077213774982255181135 27115820662473382771703)
        ·
          refine ⟨40673730993710074157555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27115820662473382771703 40673730993710074157555)
          ·
            refine ⟨61010596490565111236333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40673730993710074157555 61010596490565111236333)
            ·
              refine ⟨22878973683961916713625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61010596490565111236333 22878973683961916713625)
              ·
                refine ⟨17159230262971437535219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22878973683961916713625 17159230262971437535219)
                ·
                  refine ⟨25738845394457156302829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17159230262971437535219 25738845394457156302829)
                  ·
                    refine ⟨9652067022921433613561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25738845394457156302829 9652067022921433613561)
                    ·
                      refine ⟨7239050267191075210171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9652067022921433613561 7239050267191075210171)
                      ·
                        rfl

theorem cell23_14098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_14098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14098 prefixEnd_14098 := by exact prefixLift 14098
  have htrace : WordTrace (prefixWord ++ tailWord_14098) baseStart_14098 baseEnd_14098 := by
    simpa [prefixWord, tailWord_14098, baseEnd_14098] using wordTrace_append hprefix tailTrace_14098
  have hstable : (prefixWord ++ tailWord_14098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14098).length < 2 ^ (prefixWord ++ tailWord_14098).sum := by decide
  have hdescent : baseEnd_14098 < baseStart_14098 := by decide
  rcases family_descends (prefixWord ++ tailWord_14098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14164 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_14164 : Nat := 118140960795 + 14164 * 2 ^ 59
def prefixEnd_14164 : Nat := 4983230072969 + 3 ^ 40 * 14164 * 2
def baseEnd_14164 : Nat := 2424313330129272328289

theorem tailTrace_14164 : CollatzResearch.WordTrace tailWord_14164 prefixEnd_14164 2424313330129272328289 := by
  unfold tailWord_14164
  simp only [CollatzResearch.WordTrace]
  refine ⟨258301760346860931860773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 344402347129147909147697 258301760346860931860773)
  ·
    refine ⟨48431580065036424723895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 258301760346860931860773 48431580065036424723895)
    ·
      refine ⟨72647370097554637085843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48431580065036424723895 72647370097554637085843)
      ·
        refine ⟨108971055146331955628765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72647370097554637085843 108971055146331955628765)
        ·
          refine ⟨40864145679874483360787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108971055146331955628765 40864145679874483360787)
          ·
            refine ⟨61296218519811725041181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40864145679874483360787 61296218519811725041181)
            ·
              refine ⟨22986081944929396890443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61296218519811725041181 22986081944929396890443)
              ·
                refine ⟨34479122917394095335665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22986081944929396890443 34479122917394095335665)
                ·
                  refine ⟨25859342188045571501749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34479122917394095335665 25859342188045571501749)
                  ·
                    refine ⟨2424313330129272328289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25859342188045571501749 2424313330129272328289)
                    ·
                      rfl

theorem cell23_14164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_14164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14164 prefixEnd_14164 := by exact prefixLift 14164
  have htrace : WordTrace (prefixWord ++ tailWord_14164) baseStart_14164 baseEnd_14164 := by
    simpa [prefixWord, tailWord_14164, baseEnd_14164] using wordTrace_append hprefix tailTrace_14164
  have hstable : (prefixWord ++ tailWord_14164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14164).length < 2 ^ (prefixWord ++ tailWord_14164).sum := by decide
  have hdescent : baseEnd_14164 < baseStart_14164 := by decide
  rcases family_descends (prefixWord ++ tailWord_14164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14177 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 5, 4]
def baseStart_14177 : Nat := 118140960795 + 14177 * 2 ^ 59
def prefixEnd_14177 : Nat := 4983230072969 + 3 ^ 40 * 14177 * 2
def baseEnd_14177 : Nat := 2426538412965422040769

theorem tailTrace_14177 : CollatzResearch.WordTrace tailWord_14177 prefixEnd_14177 2426538412965422040769 := by
  unfold tailWord_14177
  simp only [CollatzResearch.WordTrace]
  refine ⟨517077669646625083944785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 344718446431083389296523 517077669646625083944785)
  ·
    refine ⟨387808252234968812958589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 517077669646625083944785 387808252234968812958589)
    ·
      refine ⟨145428094588113304859471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 387808252234968812958589 145428094588113304859471)
      ·
        refine ⟨218142141882169957289207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145428094588113304859471 218142141882169957289207)
        ·
          refine ⟨327213212823254935933811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218142141882169957289207 327213212823254935933811)
          ·
            refine ⟨490819819234882403900717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327213212823254935933811 490819819234882403900717)
            ·
              refine ⟨184057432213080901462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 490819819234882403900717 184057432213080901462769)
              ·
                refine ⟨138043074159810676097077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184057432213080901462769 138043074159810676097077)
                ·
                  refine ⟨12941538202482250884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138043074159810676097077 12941538202482250884101)
                  ·
                    refine ⟨2426538412965422040769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12941538202482250884101 2426538412965422040769)
                    ·
                      rfl

theorem cell23_14177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_14177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14177 prefixEnd_14177 := by exact prefixLift 14177
  have htrace : WordTrace (prefixWord ++ tailWord_14177) baseStart_14177 baseEnd_14177 := by
    simpa [prefixWord, tailWord_14177, baseEnd_14177] using wordTrace_append hprefix tailTrace_14177
  have hstable : (prefixWord ++ tailWord_14177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14177).length < 2 ^ (prefixWord ++ tailWord_14177).sum := by decide
  have hdescent : baseEnd_14177 < baseStart_14177 := by decide
  rcases family_descends (prefixWord ++ tailWord_14177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14184 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_14184 : Nat := 118140960795 + 14184 * 2 ^ 59
def prefixEnd_14184 : Nat := 4983230072969 + 3 ^ 40 * 14184 * 2
def baseEnd_14184 : Nat := 7283209603477738734775

theorem tailTrace_14184 : CollatzResearch.WordTrace tailWord_14184 prefixEnd_14184 7283209603477738734775 := by
  unfold tailWord_14184
  simp only [CollatzResearch.WordTrace]
  refine ⟨258666490310632639724803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 344888653747510186299737 258666490310632639724803)
  ·
    refine ⟨387999735465948959587205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258666490310632639724803 387999735465948959587205)
    ·
      refine ⟨72749950399865429922601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 387999735465948959587205 72749950399865429922601)
      ·
        refine ⟨54562462799899072441951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72749950399865429922601 54562462799899072441951)
        ·
          refine ⟨81843694199848608662927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54562462799899072441951 81843694199848608662927)
          ·
            refine ⟨122765541299772912994391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81843694199848608662927 122765541299772912994391)
            ·
              refine ⟨184148311949659369491587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122765541299772912994391 184148311949659369491587)
              ·
                refine ⟨276222467924489054237381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184148311949659369491587 276222467924489054237381)
                ·
                  refine ⟨51791712735841697669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 276222467924489054237381 51791712735841697669509)
                  ·
                    refine ⟨9710946137970318313033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51791712735841697669509 9710946137970318313033)
                    ·
                      refine ⟨7283209603477738734775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9710946137970318313033 7283209603477738734775)
                      ·
                        rfl

theorem cell23_14184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_14184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14184 prefixEnd_14184 := by exact prefixLift 14184
  have htrace : WordTrace (prefixWord ++ tailWord_14184) baseStart_14184 baseEnd_14184 := by
    simpa [prefixWord, tailWord_14184, baseEnd_14184] using wordTrace_append hprefix tailTrace_14184
  have hstable : (prefixWord ++ tailWord_14184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14184).length < 2 ^ (prefixWord ++ tailWord_14184).sum := by decide
  have hdescent : baseEnd_14184 < baseStart_14184 := by decide
  rcases family_descends (prefixWord ++ tailWord_14184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14187 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3]
def baseStart_14187 : Nat := 118140960795 + 14187 * 2 ^ 59
def prefixEnd_14187 : Nat := 4983230072969 + 3 ^ 40 * 14187 * 2
def baseEnd_14187 : Nat := 7284750045441226997261

theorem tailTrace_14187 : CollatzResearch.WordTrace tailWord_14187 prefixEnd_14187 7284750045441226997261 := by
  unfold tailWord_14187
  simp only [CollatzResearch.WordTrace]
  refine ⟨517442399610396791808815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 344961599740264527872543 517442399610396791808815)
  ·
    refine ⟨776163599415595187713223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517442399610396791808815 776163599415595187713223)
    ·
      refine ⟨1164245399123392781569835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776163599415595187713223 1164245399123392781569835)
      ·
        refine ⟨1746368098685089172354753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164245399123392781569835 1746368098685089172354753)
        ·
          refine ⟨1309776074013816879266065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746368098685089172354753 1309776074013816879266065)
          ·
            refine ⟨982332055510362659449549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309776074013816879266065 982332055510362659449549)
            ·
              refine ⟨368374520816385997293581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 982332055510362659449549 368374520816385997293581)
              ·
                refine ⟨138140445306144748985093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368374520816385997293581 138140445306144748985093)
                ·
                  refine ⟨25901333494902140434705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138140445306144748985093 25901333494902140434705)
                  ·
                    refine ⟨19426000121176605326029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25901333494902140434705 19426000121176605326029)
                    ·
                      refine ⟨7284750045441226997261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19426000121176605326029 7284750045441226997261)
                      ·
                        rfl

theorem cell23_14187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 3].length) (baseStart_14187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14187 prefixEnd_14187 := by exact prefixLift 14187
  have htrace : WordTrace (prefixWord ++ tailWord_14187) baseStart_14187 baseEnd_14187 := by
    simpa [prefixWord, tailWord_14187, baseEnd_14187] using wordTrace_append hprefix tailTrace_14187
  have hstable : (prefixWord ++ tailWord_14187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14187).length < 2 ^ (prefixWord ++ tailWord_14187).sum := by decide
  have hdescent : baseEnd_14187 < baseStart_14187 := by decide
  rcases family_descends (prefixWord ++ tailWord_14187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14197 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_14197 : Nat := 118140960795 + 14197 * 2 ^ 59
def prefixEnd_14197 : Nat := 4983230072969 + 3 ^ 40 * 14197 * 2
def baseEnd_14197 : Nat := 7289884851986187872215

theorem tailTrace_14197 : CollatzResearch.WordTrace tailWord_14197 prefixEnd_14197 7289884851986187872215 := by
  unfold tailWord_14197
  simp only [CollatzResearch.WordTrace]
  refine ⟨517807129574168499672845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 345204753049445666448563 517807129574168499672845)
  ·
    refine ⟨194177673590313187377317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 517807129574168499672845 194177673590313187377317)
    ·
      refine ⟨36408313798183722633247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194177673590313187377317 36408313798183722633247)
      ·
        refine ⟨54612470697275583949871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36408313798183722633247 54612470697275583949871)
        ·
          refine ⟨81918706045913375924807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54612470697275583949871 81918706045913375924807)
          ·
            refine ⟨122878059068870063887211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81918706045913375924807 122878059068870063887211)
            ·
              refine ⟨184317088603305095830817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122878059068870063887211 184317088603305095830817)
              ·
                refine ⟨138237816452478821873113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184317088603305095830817 138237816452478821873113)
                ·
                  refine ⟨103678362339359116404835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138237816452478821873113 103678362339359116404835)
                  ·
                    refine ⟨155517543509038674607253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103678362339359116404835 155517543509038674607253)
                    ·
                      refine ⟨7289884851986187872215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 155517543509038674607253 7289884851986187872215)
                      ·
                        rfl

theorem cell23_14197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_14197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14197 prefixEnd_14197 := by exact prefixLift 14197
  have htrace : WordTrace (prefixWord ++ tailWord_14197) baseStart_14197 baseEnd_14197 := by
    simpa [prefixWord, tailWord_14197, baseEnd_14197] using wordTrace_append hprefix tailTrace_14197
  have hstable : (prefixWord ++ tailWord_14197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14197).length < 2 ^ (prefixWord ++ tailWord_14197).sum := by decide
  have hdescent : baseEnd_14197 < baseStart_14197 := by decide
  rcases family_descends (prefixWord ++ tailWord_14197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14200 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_14200 : Nat := 118140960795 + 14200 * 2 ^ 59
def prefixEnd_14200 : Nat := 4983230072969 + 3 ^ 40 * 14200 * 2
def baseEnd_14200 : Nat := 7291425293949676134701

theorem tailTrace_14200 : CollatzResearch.WordTrace tailWord_14200 prefixEnd_14200 7291425293949676134701 := by
  unfold tailWord_14200
  simp only [CollatzResearch.WordTrace]
  refine ⟨258958274281650006016027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 345277699042200008021369 258958274281650006016027)
  ·
    refine ⟨388437411422475009024041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 258958274281650006016027 388437411422475009024041)
    ·
      refine ⟨291328058566856256768031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388437411422475009024041 291328058566856256768031)
      ·
        refine ⟨436992087850284385152047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291328058566856256768031 436992087850284385152047)
        ·
          refine ⟨655488131775426577728071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436992087850284385152047 655488131775426577728071)
          ·
            refine ⟨983232197663139866592107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655488131775426577728071 983232197663139866592107)
            ·
              refine ⟨1474848296494709799888161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983232197663139866592107 1474848296494709799888161)
              ·
                refine ⟨1106136222371032349916121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474848296494709799888161 1106136222371032349916121)
                ·
                  refine ⟨829602166778274262437091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1106136222371032349916121 829602166778274262437091)
                  ·
                    refine ⟨1244403250167411393655637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 829602166778274262437091 1244403250167411393655637)
                    ·
                      refine ⟨7291425293949676134701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 1244403250167411393655637 7291425293949676134701)
                      ·
                        rfl

theorem cell23_14200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_14200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14200 prefixEnd_14200 := by exact prefixLift 14200
  have htrace : WordTrace (prefixWord ++ tailWord_14200) baseStart_14200 baseEnd_14200 := by
    simpa [prefixWord, tailWord_14200, baseEnd_14200] using wordTrace_append hprefix tailTrace_14200
  have hstable : (prefixWord ++ tailWord_14200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14200).length < 2 ^ (prefixWord ++ tailWord_14200).sum := by decide
  have hdescent : baseEnd_14200 < baseStart_14200 := by decide
  rcases family_descends (prefixWord ++ tailWord_14200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14217 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_14217 : Nat := 118140960795 + 14217 * 2 ^ 59
def prefixEnd_14217 : Nat := 4983230072969 + 3 ^ 40 * 14217 * 2
def baseEnd_14217 : Nat := 7300154465076109622123

theorem tailTrace_14217 : CollatzResearch.WordTrace tailWord_14217 prefixEnd_14217 7300154465076109622123 := by
  unfold tailWord_14217
  simp only [CollatzResearch.WordTrace]
  refine ⟨518536589501711915400905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 345691059667807943600603 518536589501711915400905)
  ·
    refine ⟨388902442126283936550679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 518536589501711915400905 388902442126283936550679)
    ·
      refine ⟨583353663189425904826019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388902442126283936550679 583353663189425904826019)
      ·
        refine ⟨875030494784138857239029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583353663189425904826019 875030494784138857239029)
        ·
          refine ⟨82034108886013017866159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 875030494784138857239029 82034108886013017866159)
          ·
            refine ⟨123051163329019526799239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82034108886013017866159 123051163329019526799239)
            ·
              refine ⟨184576744993529290198859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123051163329019526799239 184576744993529290198859)
              ·
                refine ⟨276865117490293935298289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184576744993529290198859 276865117490293935298289)
                ·
                  refine ⟨207648838117720451473717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276865117490293935298289 207648838117720451473717)
                  ·
                    refine ⟨19467078573536292325661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 207648838117720451473717 19467078573536292325661)
                    ·
                      refine ⟨7300154465076109622123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19467078573536292325661 7300154465076109622123)
                      ·
                        rfl

theorem cell23_14217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_14217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14217 prefixEnd_14217 := by exact prefixLift 14217
  have htrace : WordTrace (prefixWord ++ tailWord_14217) baseStart_14217 baseEnd_14217 := by
    simpa [prefixWord, tailWord_14217, baseEnd_14217] using wordTrace_append hprefix tailTrace_14217
  have hstable : (prefixWord ++ tailWord_14217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14217).length < 2 ^ (prefixWord ++ tailWord_14217).sum := by decide
  have hdescent : baseEnd_14217 < baseStart_14217 := by decide
  rcases family_descends (prefixWord ++ tailWord_14217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14228 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_14228 : Nat := 118140960795 + 14228 * 2 ^ 59
def prefixEnd_14228 : Nat := 4983230072969 + 3 ^ 40 * 14228 * 2
def baseEnd_14228 : Nat := 2435267584091855528191

theorem tailTrace_14228 : CollatzResearch.WordTrace tailWord_14228 prefixEnd_14228 2435267584091855528191 := by
  unfold tailWord_14228
  simp only [CollatzResearch.WordTrace]
  refine ⟨259468896230930397025669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 345958528307907196034225 259468896230930397025669)
  ·
    refine ⟨48650418043299449442313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259468896230930397025669 48650418043299449442313)
    ·
      refine ⟨36487813532474587081735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48650418043299449442313 36487813532474587081735)
      ·
        refine ⟨54731720298711880622603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36487813532474587081735 54731720298711880622603)
        ·
          refine ⟨82097580448067820933905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54731720298711880622603 82097580448067820933905)
          ·
            refine ⟨61573185336050865700429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82097580448067820933905 61573185336050865700429)
            ·
              refine ⟨23089944501019074637661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61573185336050865700429 23089944501019074637661)
              ·
                refine ⟨8658729187882152989123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23089944501019074637661 8658729187882152989123)
                ·
                  refine ⟨12988093781823229483685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8658729187882152989123 12988093781823229483685)
                  ·
                    refine ⟨2435267584091855528191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12988093781823229483685 2435267584091855528191)
                    ·
                      rfl

theorem cell23_14228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_14228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14228 prefixEnd_14228 := by exact prefixLift 14228
  have htrace : WordTrace (prefixWord ++ tailWord_14228) baseStart_14228 baseEnd_14228 := by
    simpa [prefixWord, tailWord_14228, baseEnd_14228] using wordTrace_append hprefix tailTrace_14228
  have hstable : (prefixWord ++ tailWord_14228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14228).length < 2 ^ (prefixWord ++ tailWord_14228).sum := by decide
  have hdescent : baseEnd_14228 < baseStart_14228 := by decide
  rcases family_descends (prefixWord ++ tailWord_14228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14284 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_14284 : Nat := 118140960795 + 14284 * 2 ^ 59
def prefixEnd_14284 : Nat := 4983230072969 + 3 ^ 40 * 14284 * 2
def baseEnd_14284 : Nat := 2444852556309115828105

theorem tailTrace_14284 : CollatzResearch.WordTrace tailWord_14284 prefixEnd_14284 2444852556309115828105 := by
  unfold tailWord_14284
  simp only [CollatzResearch.WordTrace]
  refine ⟨260490140129491179044953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 347320186839321572059937 260490140129491179044953)
  ·
    refine ⟨195367605097118384283715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260490140129491179044953 195367605097118384283715)
    ·
      refine ⟨293051407645677576425573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195367605097118384283715 293051407645677576425573)
      ·
        refine ⟨54947138933564545579795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293051407645677576425573 54947138933564545579795)
        ·
          refine ⟨82420708400346818369693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54947138933564545579795 82420708400346818369693)
          ·
            refine ⟨30907765650130056888635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82420708400346818369693 30907765650130056888635)
            ·
              refine ⟨46361648475195085332953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30907765650130056888635 46361648475195085332953)
              ·
                refine ⟨34771236356396313999715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46361648475195085332953 34771236356396313999715)
                ·
                  refine ⟨52156854534594470999573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34771236356396313999715 52156854534594470999573)
                  ·
                    refine ⟨2444852556309115828105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52156854534594470999573 2444852556309115828105)
                    ·
                      rfl

theorem cell23_14284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_14284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14284 prefixEnd_14284 := by exact prefixLift 14284
  have htrace : WordTrace (prefixWord ++ tailWord_14284) baseStart_14284 baseEnd_14284 := by
    simpa [prefixWord, tailWord_14284, baseEnd_14284] using wordTrace_append hprefix tailTrace_14284
  have hstable : (prefixWord ++ tailWord_14284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14284).length < 2 ^ (prefixWord ++ tailWord_14284).sum := by decide
  have hdescent : baseEnd_14284 < baseStart_14284 := by decide
  rcases family_descends (prefixWord ++ tailWord_14284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14297 : List Nat := [1, 2, 1, 2, 6, 11]
def baseStart_14297 : Nat := 118140960795 + 14297 * 2 ^ 59
def prefixEnd_14297 : Nat := 4983230072969 + 3 ^ 40 * 14297 * 2
def baseEnd_14297 : Nat := 30210835051176117785

theorem tailTrace_14297 : CollatzResearch.WordTrace tailWord_14297 prefixEnd_14297 30210835051176117785 := by
  unfold tailWord_14297
  simp only [CollatzResearch.WordTrace]
  refine ⟨521454429211885578313145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 347636286141257052208763 521454429211885578313145)
  ·
    refine ⟨391090821908914183734859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 521454429211885578313145 391090821908914183734859)
    ·
      refine ⟨586636232863371275602289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391090821908914183734859 586636232863371275602289)
      ·
        refine ⟨439977174647528456701717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586636232863371275602289 439977174647528456701717)
        ·
          refine ⟨20623930061602896407893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 439977174647528456701717 20623930061602896407893)
          ·
            refine ⟨30210835051176117785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 20623930061602896407893 30210835051176117785)
            ·
              rfl

theorem cell23_14297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 11].length) (baseStart_14297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14297 prefixEnd_14297 := by exact prefixLift 14297
  have htrace : WordTrace (prefixWord ++ tailWord_14297) baseStart_14297 baseEnd_14297 := by
    simpa [prefixWord, tailWord_14297, baseEnd_14297] using wordTrace_append hprefix tailTrace_14297
  have hstable : (prefixWord ++ tailWord_14297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14297).length < 2 ^ (prefixWord ++ tailWord_14297).sum := by decide
  have hdescent : baseEnd_14297 < baseStart_14297 := by decide
  rcases family_descends (prefixWord ++ tailWord_14297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14321 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_14321 : Nat := 118140960795 + 14321 * 2 ^ 59
def prefixEnd_14321 : Nat := 4983230072969 + 3 ^ 40 * 14321 * 2
def baseEnd_14321 : Nat := 7353556453143702721645

theorem tailTrace_14321 : CollatzResearch.WordTrace tailWord_14321 prefixEnd_14321 7353556453143702721645 := by
  unfold tailWord_14321
  simp only [CollatzResearch.WordTrace]
  refine ⟨522329781124937677186817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 348219854083291784791211 522329781124937677186817)
  ·
    refine ⟨391747335843703257890113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 522329781124937677186817 391747335843703257890113)
    ·
      refine ⟨293810501882777443417585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391747335843703257890113 293810501882777443417585)
      ·
        refine ⟨220357876412083082563189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293810501882777443417585 220357876412083082563189)
        ·
          refine ⟨20658550913632788990299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220357876412083082563189 20658550913632788990299)
          ·
            refine ⟨30987826370449183485449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20658550913632788990299 30987826370449183485449)
            ·
              refine ⟨23240869777836887614087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30987826370449183485449 23240869777836887614087)
              ·
                refine ⟨34861304666755331421131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23240869777836887614087 34861304666755331421131)
                ·
                  refine ⟨52291957000132997131697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34861304666755331421131 52291957000132997131697)
                  ·
                    refine ⟨39218967750099747848773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52291957000132997131697 39218967750099747848773)
                    ·
                      refine ⟨7353556453143702721645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 39218967750099747848773 7353556453143702721645)
                      ·
                        rfl

theorem cell23_14321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_14321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14321 prefixEnd_14321 := by exact prefixLift 14321
  have htrace : WordTrace (prefixWord ++ tailWord_14321) baseStart_14321 baseEnd_14321 := by
    simpa [prefixWord, tailWord_14321, baseEnd_14321] using wordTrace_append hprefix tailTrace_14321
  have hstable : (prefixWord ++ tailWord_14321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14321).length < 2 ^ (prefixWord ++ tailWord_14321).sum := by decide
  have hdescent : baseEnd_14321 < baseStart_14321 := by decide
  rcases family_descends (prefixWord ++ tailWord_14321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14375 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_14375 : Nat := 118140960795 + 14375 * 2 ^ 59
def prefixEnd_14375 : Nat := 4983230072969 + 3 ^ 40 * 14375 * 2
def baseEnd_14375 : Nat := 7381284408486491446397

theorem tailTrace_14375 : CollatzResearch.WordTrace tailWord_14375 prefixEnd_14375 7381284408486491446397 := by
  unfold tailWord_14375
  simp only [CollatzResearch.WordTrace]
  refine ⟨524299322929304899652579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 349532881952869933101719 524299322929304899652579)
  ·
    refine ⟨786448984393957349478869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524299322929304899652579 786448984393957349478869)
    ·
      refine ⟨18432398071733375378411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 786448984393957349478869 18432398071733375378411)
      ·
        refine ⟨27648597107600063067617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18432398071733375378411 27648597107600063067617)
        ·
          refine ⟨20736447830700047300713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27648597107600063067617 20736447830700047300713)
          ·
            refine ⟨15552335873025035475535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20736447830700047300713 15552335873025035475535)
            ·
              refine ⟨23328503809537553213303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15552335873025035475535 23328503809537553213303)
              ·
                refine ⟨34992755714306329819955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23328503809537553213303 34992755714306329819955)
                ·
                  refine ⟨52489133571459494729933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34992755714306329819955 52489133571459494729933)
                  ·
                    refine ⟨19683425089297310523725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52489133571459494729933 19683425089297310523725)
                    ·
                      refine ⟨7381284408486491446397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 19683425089297310523725 7381284408486491446397)
                      ·
                        rfl

theorem cell23_14375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_14375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14375 prefixEnd_14375 := by exact prefixLift 14375
  have htrace : WordTrace (prefixWord ++ tailWord_14375) baseStart_14375 baseEnd_14375 := by
    simpa [prefixWord, tailWord_14375, baseEnd_14375] using wordTrace_append hprefix tailTrace_14375
  have hstable : (prefixWord ++ tailWord_14375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14375).length < 2 ^ (prefixWord ++ tailWord_14375).sum := by decide
  have hdescent : baseEnd_14375 < baseStart_14375 := by decide
  rcases family_descends (prefixWord ++ tailWord_14375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14401 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_14401 : Nat := 118140960795 + 14401 * 2 ^ 59
def prefixEnd_14401 : Nat := 4983230072969 + 3 ^ 40 * 14401 * 2
def baseEnd_14401 : Nat := 7394634905503389721277

theorem tailTrace_14401 : CollatzResearch.WordTrace tailWord_14401 prefixEnd_14401 7394634905503389721277 := by
  unfold tailWord_14401
  simp only [CollatzResearch.WordTrace]
  refine ⟨525247620835111340099057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350165080556740893399371 525247620835111340099057)
  ·
    refine ⟨393935715626333505074293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 525247620835111340099057 393935715626333505074293)
    ·
      refine ⟨36931473339968766100715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393935715626333505074293 36931473339968766100715)
      ·
        refine ⟨55397210009953149151073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36931473339968766100715 55397210009953149151073)
        ·
          refine ⟨41547907507464861863305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55397210009953149151073 41547907507464861863305)
          ·
            refine ⟨31160930630598646397479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41547907507464861863305 31160930630598646397479)
            ·
              refine ⟨46741395945897969596219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31160930630598646397479 46741395945897969596219)
              ·
                refine ⟨70112093918846954394329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46741395945897969596219 70112093918846954394329)
                ·
                  refine ⟨52584070439135215795747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70112093918846954394329 52584070439135215795747)
                  ·
                    refine ⟨78876105658702823693621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52584070439135215795747 78876105658702823693621)
                    ·
                      refine ⟨7394634905503389721277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 78876105658702823693621 7394634905503389721277)
                      ·
                        rfl

theorem cell23_14401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_14401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14401 prefixEnd_14401 := by exact prefixLift 14401
  have htrace : WordTrace (prefixWord ++ tailWord_14401) baseStart_14401 baseEnd_14401 := by
    simpa [prefixWord, tailWord_14401, baseEnd_14401] using wordTrace_append hprefix tailTrace_14401
  have hstable : (prefixWord ++ tailWord_14401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14401).length < 2 ^ (prefixWord ++ tailWord_14401).sum := by decide
  have hdescent : baseEnd_14401 < baseStart_14401 := by decide
  rcases family_descends (prefixWord ++ tailWord_14401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14421 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 7]
def baseStart_14421 : Nat := 118140960795 + 14421 * 2 ^ 59
def prefixEnd_14421 : Nat := 4983230072969 + 3 ^ 40 * 14421 * 2
def baseEnd_14421 : Nat := 822767168732590163465

theorem tailTrace_14421 : CollatzResearch.WordTrace tailWord_14421 prefixEnd_14421 822767168732590163465 := by
  unfold tailWord_14421
  simp only [CollatzResearch.WordTrace]
  refine ⟨525977080762654755827117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 350651387175103170551411 525977080762654755827117)
  ·
    refine ⟨197241405285995533435169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 525977080762654755827117 197241405285995533435169)
    ·
      refine ⟨147931053964496650076377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197241405285995533435169 147931053964496650076377)
      ·
        refine ⟨110948290473372487557283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147931053964496650076377 110948290473372487557283)
        ·
          refine ⟨166422435710058731335925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110948290473372487557283 166422435710058731335925)
          ·
            refine ⟨15602103347818006062743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166422435710058731335925 15602103347818006062743)
            ·
              refine ⟨23403155021727009094115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15602103347818006062743 23403155021727009094115)
              ·
                refine ⟨35104732532590513641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23403155021727009094115 35104732532590513641173)
                ·
                  refine ⟨822767168732590163465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35104732532590513641173 822767168732590163465)
                  ·
                    rfl

theorem cell23_14421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_14421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14421 prefixEnd_14421 := by exact prefixLift 14421
  have htrace : WordTrace (prefixWord ++ tailWord_14421) baseStart_14421 baseEnd_14421 := by
    simpa [prefixWord, tailWord_14421, baseEnd_14421] using wordTrace_append hprefix tailTrace_14421
  have hstable : (prefixWord ++ tailWord_14421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14421).length < 2 ^ (prefixWord ++ tailWord_14421).sum := by decide
  have hdescent : baseEnd_14421 < baseStart_14421 := by decide
  rcases family_descends (prefixWord ++ tailWord_14421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14432 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2]
def baseStart_14432 : Nat := 118140960795 + 14432 * 2 ^ 59
def prefixEnd_14432 : Nat := 4983230072969 + 3 ^ 40 * 14432 * 2
def baseEnd_14432 : Nat := 7410552805792768433635

theorem tailTrace_14432 : CollatzResearch.WordTrace tailWord_14432 prefixEnd_14432 7410552805792768433635 := by
  unfold tailWord_14432
  simp only [CollatzResearch.WordTrace]
  refine ⟨263189141861401817238775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 350918855815202422985033 263189141861401817238775)
  ·
    refine ⟨394783712792102725858163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263189141861401817238775 394783712792102725858163)
    ·
      refine ⟨592175569188154088787245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394783712792102725858163 592175569188154088787245)
      ·
        refine ⟨222065838445557783295217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 592175569188154088787245 222065838445557783295217)
        ·
          refine ⟨166549378834168337471413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222065838445557783295217 166549378834168337471413)
          ·
            refine ⟨15614004265703281637945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 166549378834168337471413 15614004265703281637945)
            ·
              refine ⟨11710503199277461228459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15614004265703281637945 11710503199277461228459)
              ·
                refine ⟨17565754798916191842689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11710503199277461228459 17565754798916191842689)
                ·
                  refine ⟨13174316099187143882017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17565754798916191842689 13174316099187143882017)
                  ·
                    refine ⟨9880737074390357911513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13174316099187143882017 9880737074390357911513)
                    ·
                      refine ⟨7410552805792768433635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 9880737074390357911513 7410552805792768433635)
                      ·
                        rfl

theorem cell23_14432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_14432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14432 prefixEnd_14432 := by exact prefixLift 14432
  have htrace : WordTrace (prefixWord ++ tailWord_14432) baseStart_14432 baseEnd_14432 := by
    simpa [prefixWord, tailWord_14432, baseEnd_14432] using wordTrace_append hprefix tailTrace_14432
  have hstable : (prefixWord ++ tailWord_14432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14432).length < 2 ^ (prefixWord ++ tailWord_14432).sum := by decide
  have hdescent : baseEnd_14432 < baseStart_14432 := by decide
  rcases family_descends (prefixWord ++ tailWord_14432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14471 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_14471 : Nat := 118140960795 + 14471 * 2 ^ 59
def prefixEnd_14471 : Nat := 4983230072969 + 3 ^ 40 * 14471 * 2
def baseEnd_14471 : Nat := 7430578551318115845955

theorem tailTrace_14471 : CollatzResearch.WordTrace tailWord_14471 prefixEnd_14471 7430578551318115845955 := by
  unfold tailWord_14471
  simp only [CollatzResearch.WordTrace]
  refine ⟨527800730581513295147267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 351867153721008863431511 527800730581513295147267)
  ·
    refine ⟨791701095872269942720901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 527800730581513295147267 791701095872269942720901)
    ·
      refine ⟨148443955476050614260169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 791701095872269942720901 148443955476050614260169)
      ·
        refine ⟨111332966607037960695127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148443955476050614260169 111332966607037960695127)
        ·
          refine ⟨166999449910556941042691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111332966607037960695127 166999449910556941042691)
          ·
            refine ⟨250499174865835411564037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166999449910556941042691 250499174865835411564037)
            ·
              refine ⟨46968595287344139668257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250499174865835411564037 46968595287344139668257)
              ·
                refine ⟨35226446465508104751193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46968595287344139668257 35226446465508104751193)
                ·
                  refine ⟨26419834849131078563395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35226446465508104751193 26419834849131078563395)
                  ·
                    refine ⟨39629752273696617845093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26419834849131078563395 39629752273696617845093)
                    ·
                      refine ⟨7430578551318115845955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 39629752273696617845093 7430578551318115845955)
                      ·
                        rfl

theorem cell23_14471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_14471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14471 prefixEnd_14471 := by exact prefixLift 14471
  have htrace : WordTrace (prefixWord ++ tailWord_14471) baseStart_14471 baseEnd_14471 := by
    simpa [prefixWord, tailWord_14471, baseEnd_14471] using wordTrace_append hprefix tailTrace_14471
  have hstable : (prefixWord ++ tailWord_14471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14471).length < 2 ^ (prefixWord ++ tailWord_14471).sum := by decide
  have hdescent : baseEnd_14471 < baseStart_14471 := by decide
  rcases family_descends (prefixWord ++ tailWord_14471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14498 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_14498 : Nat := 118140960795 + 14498 * 2 ^ 59
def prefixEnd_14498 : Nat := 4983230072969 + 3 ^ 40 * 14498 * 2
def baseEnd_14498 : Nat := 2481480842996503402777

theorem tailTrace_14498 : CollatzResearch.WordTrace tailWord_14498 prefixEnd_14498 2481480842996503402777 := by
  unfold tailWord_14498
  simp only [CollatzResearch.WordTrace]
  refine ⟨132196375370924226595037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 352523667655797937586765 132196375370924226595037)
  ·
    refine ⟨49573640764096584973139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132196375370924226595037 49573640764096584973139)
    ·
      refine ⟨74360461146144877459709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49573640764096584973139 74360461146144877459709)
      ·
        refine ⟨27885172929804329047391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74360461146144877459709 27885172929804329047391)
        ·
          refine ⟨41827759394706493571087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27885172929804329047391 41827759394706493571087)
          ·
            refine ⟨62741639092059740356631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41827759394706493571087 62741639092059740356631)
            ·
              refine ⟨94112458638089610534947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62741639092059740356631 94112458638089610534947)
              ·
                refine ⟨141168687957134415802421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94112458638089610534947 141168687957134415802421)
                ·
                  refine ⟨13234564495981351481477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141168687957134415802421 13234564495981351481477)
                  ·
                    refine ⟨2481480842996503402777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13234564495981351481477 2481480842996503402777)
                    ·
                      rfl

theorem cell23_14498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_14498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14498 prefixEnd_14498 := by exact prefixLift 14498
  have htrace : WordTrace (prefixWord ++ tailWord_14498) baseStart_14498 baseEnd_14498 := by
    simpa [prefixWord, tailWord_14498, baseEnd_14498] using wordTrace_append hprefix tailTrace_14498
  have hstable : (prefixWord ++ tailWord_14498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14498).length < 2 ^ (prefixWord ++ tailWord_14498).sum := by decide
  have hdescent : baseEnd_14498 < baseStart_14498 := by decide
  rcases family_descends (prefixWord ++ tailWord_14498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14528 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 6]
def baseStart_14528 : Nat := 118140960795 + 14528 * 2 ^ 59
def prefixEnd_14528 : Nat := 4983230072969 + 3 ^ 40 * 14528 * 2
def baseEnd_14528 : Nat := 828871883180488092577

theorem tailTrace_14528 : CollatzResearch.WordTrace tailWord_14528 prefixEnd_14528 828871883180488092577 := by
  unfold tailWord_14528
  simp only [CollatzResearch.WordTrace]
  refine ⟨264939845687506014986119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 353253127583341353314825 264939845687506014986119)
  ·
    refine ⟨397409768531259022479179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264939845687506014986119 397409768531259022479179)
    ·
      refine ⟨596114652796888533718769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397409768531259022479179 596114652796888533718769)
      ·
        refine ⟨447085989597666400289077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596114652796888533718769 447085989597666400289077)
        ·
          refine ⟨41914311524781225027101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 447085989597666400289077 41914311524781225027101)
          ·
            refine ⟨15717866821792959385163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41914311524781225027101 15717866821792959385163)
            ·
              refine ⟨23576800232689439077745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717866821792959385163 23576800232689439077745)
              ·
                refine ⟨17682600174517079308309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23576800232689439077745 17682600174517079308309)
                ·
                  refine ⟨828871883180488092577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17682600174517079308309 828871883180488092577)
                  ·
                    rfl

theorem cell23_14528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_14528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14528 prefixEnd_14528 := by exact prefixLift 14528
  have htrace : WordTrace (prefixWord ++ tailWord_14528) baseStart_14528 baseEnd_14528 := by
    simpa [prefixWord, tailWord_14528, baseEnd_14528] using wordTrace_append hprefix tailTrace_14528
  have hstable : (prefixWord ++ tailWord_14528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14528).length < 2 ^ (prefixWord ++ tailWord_14528).sum := by decide
  have hdescent : baseEnd_14528 < baseStart_14528 := by decide
  rcases family_descends (prefixWord ++ tailWord_14528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14571 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 6, 4]
def baseStart_14571 : Nat := 118140960795 + 14571 * 2 ^ 59
def prefixEnd_14571 : Nat := 4983230072969 + 3 ^ 40 * 14571 * 2
def baseEnd_14571 : Nat := 2493975538922574865165

theorem tailTrace_14571 : CollatzResearch.WordTrace tailWord_14571 prefixEnd_14571 2493975538922574865165 := by
  unfold tailWord_14571
  simp only [CollatzResearch.WordTrace]
  refine ⟨531448030219230373787567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 354298686812820249191711 531448030219230373787567)
  ·
    refine ⟨797172045328845560681351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 531448030219230373787567 797172045328845560681351)
    ·
      refine ⟨1195758067993268341022027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797172045328845560681351 1195758067993268341022027)
      ·
        refine ⟨1793637101989902511533041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195758067993268341022027 1793637101989902511533041)
        ·
          refine ⟨1345227826492426883649781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793637101989902511533041 1345227826492426883649781)
          ·
            refine ⟨126115108733665020342167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1345227826492426883649781 126115108733665020342167)
            ·
              refine ⟨189172663100497530513251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126115108733665020342167 189172663100497530513251)
              ·
                refine ⟨283758994650746295769877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189172663100497530513251 283758994650746295769877)
                ·
                  refine ⟨13301202874253732614213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 283758994650746295769877 13301202874253732614213)
                  ·
                    refine ⟨2493975538922574865165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13301202874253732614213 2493975538922574865165)
                    ·
                      rfl

theorem cell23_14571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 4].length) (baseStart_14571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14571 prefixEnd_14571 := by exact prefixLift 14571
  have htrace : WordTrace (prefixWord ++ tailWord_14571) baseStart_14571 baseEnd_14571 := by
    simpa [prefixWord, tailWord_14571, baseEnd_14571] using wordTrace_append hprefix tailTrace_14571
  have hstable : (prefixWord ++ tailWord_14571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14571).length < 2 ^ (prefixWord ++ tailWord_14571).sum := by decide
  have hdescent : baseEnd_14571 < baseStart_14571 := by decide
  rcases family_descends (prefixWord ++ tailWord_14571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14588 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_14588 : Nat := 118140960795 + 14588 * 2 ^ 59
def prefixEnd_14588 : Nat := 4983230072969 + 3 ^ 40 * 14588 * 2
def baseEnd_14588 : Nat := 2496885262631386027639

theorem tailTrace_14588 : CollatzResearch.WordTrace tailWord_14588 prefixEnd_14588 2496885262631386027639 := by
  unfold tailWord_14588
  simp only [CollatzResearch.WordTrace]
  refine ⟨266034035578821138578209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 354712047438428184770945 266034035578821138578209)
  ·
    refine ⟨199525526684115853933657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266034035578821138578209 199525526684115853933657)
    ·
      refine ⟨149644145013086890450243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199525526684115853933657 149644145013086890450243)
      ·
        refine ⟨224466217519630335675365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149644145013086890450243 224466217519630335675365)
        ·
          refine ⟨42087415784930687939131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224466217519630335675365 42087415784930687939131)
          ·
            refine ⟨63131123677396031908697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42087415784930687939131 63131123677396031908697)
            ·
              refine ⟨47348342758047023931523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63131123677396031908697 47348342758047023931523)
              ·
                refine ⟨71022514137070535897285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47348342758047023931523 71022514137070535897285)
                ·
                  refine ⟨13316721400700725480741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71022514137070535897285 13316721400700725480741)
                  ·
                    refine ⟨2496885262631386027639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13316721400700725480741 2496885262631386027639)
                    ·
                      rfl

theorem cell23_14588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_14588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14588 prefixEnd_14588 := by exact prefixLift 14588
  have htrace : WordTrace (prefixWord ++ tailWord_14588) baseStart_14588 baseEnd_14588 := by
    simpa [prefixWord, tailWord_14588, baseEnd_14588] using wordTrace_append hprefix tailTrace_14588
  have hstable : (prefixWord ++ tailWord_14588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14588).length < 2 ^ (prefixWord ++ tailWord_14588).sum := by decide
  have hdescent : baseEnd_14588 < baseStart_14588 := by decide
  rcases family_descends (prefixWord ++ tailWord_14588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14601 : List Nat := [1, 2, 1, 1, 3, 5, 2, 8]
def baseStart_14601 : Nat := 118140960795 + 14601 * 2 ^ 59
def prefixEnd_14601 : Nat := 4983230072969 + 3 ^ 40 * 14601 * 2
def baseEnd_14601 : Nat := 277678927274170637791

theorem tailTrace_14601 : CollatzResearch.WordTrace tailWord_14601 prefixEnd_14601 277678927274170637791 := by
  unfold tailWord_14601
  simp only [CollatzResearch.WordTrace]
  refine ⟨532542220110545497379657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 355028146740363664919771 532542220110545497379657)
  ·
    refine ⟨399406665082909123034743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 532542220110545497379657 399406665082909123034743)
    ·
      refine ⟨599109997624363684552115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399406665082909123034743 599109997624363684552115)
      ·
        refine ⟨898664996436545526828173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599109997624363684552115 898664996436545526828173)
        ·
          refine ⟨336999373663704572560565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 898664996436545526828173 336999373663704572560565)
          ·
            refine ⟨31593691280972303677553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336999373663704572560565 31593691280972303677553)
            ·
              refine ⟨23695268460729227758165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31593691280972303677553 23695268460729227758165)
              ·
                refine ⟨277678927274170637791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 23695268460729227758165 277678927274170637791)
                ·
                  rfl

theorem cell23_14601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 8].length) (baseStart_14601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14601 prefixEnd_14601 := by exact prefixLift 14601
  have htrace : WordTrace (prefixWord ++ tailWord_14601) baseStart_14601 baseEnd_14601 := by
    simpa [prefixWord, tailWord_14601, baseEnd_14601] using wordTrace_append hprefix tailTrace_14601
  have hstable : (prefixWord ++ tailWord_14601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14601).length < 2 ^ (prefixWord ++ tailWord_14601).sum := by decide
  have hdescent : baseEnd_14601 < baseStart_14601 := by decide
  rcases family_descends (prefixWord ++ tailWord_14601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3]
def baseStart_14611 : Nat := 118140960795 + 14611 * 2 ^ 59
def prefixEnd_14611 : Nat := 4983230072969 + 3 ^ 40 * 14611 * 2
def baseEnd_14611 : Nat := 7502465842947568095311

theorem tailTrace_14611 : CollatzResearch.WordTrace tailWord_14611 prefixEnd_14611 7502465842947568095311 := by
  unfold tailWord_14611
  simp only [CollatzResearch.WordTrace]
  refine ⟨532906950074317205243687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 355271300049544803495791 532906950074317205243687)
  ·
    refine ⟨799360425111475807865531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532906950074317205243687 799360425111475807865531)
    ·
      refine ⟨1199040637667213711798297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799360425111475807865531 1199040637667213711798297)
      ·
        refine ⟨899280478250410283848723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199040637667213711798297 899280478250410283848723)
        ·
          refine ⟨1348920717375615425773085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899280478250410283848723 1348920717375615425773085)
          ·
            refine ⟨505845269015855784664907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1348920717375615425773085 505845269015855784664907)
            ·
              refine ⟨758767903523783676997361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505845269015855784664907 758767903523783676997361)
              ·
                refine ⟨569075927642837757748021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758767903523783676997361 569075927642837757748021)
                ·
                  refine ⟨53350868216516039788877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 569075927642837757748021 53350868216516039788877)
                  ·
                    refine ⟨20006575581193514920829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53350868216516039788877 20006575581193514920829)
                    ·
                      refine ⟨7502465842947568095311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20006575581193514920829 7502465842947568095311)
                      ·
                        rfl

theorem cell23_14611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_14611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14611 prefixEnd_14611 := by exact prefixLift 14611
  have htrace : WordTrace (prefixWord ++ tailWord_14611) baseStart_14611 baseEnd_14611 := by
    simpa [prefixWord, tailWord_14611, baseEnd_14611] using wordTrace_append hprefix tailTrace_14611
  have hstable : (prefixWord ++ tailWord_14611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14611).length < 2 ^ (prefixWord ++ tailWord_14611).sum := by decide
  have hdescent : baseEnd_14611 < baseStart_14611 := by decide
  rcases family_descends (prefixWord ++ tailWord_14611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14615 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_14615 : Nat := 118140960795 + 14615 * 2 ^ 59
def prefixEnd_14615 : Nat := 4983230072969 + 3 ^ 40 * 14615 * 2
def baseEnd_14615 : Nat := 7504519765565552445293

theorem tailTrace_14615 : CollatzResearch.WordTrace tailWord_14615 prefixEnd_14615 7504519765565552445293 := by
  unfold tailWord_14615
  simp only [CollatzResearch.WordTrace]
  refine ⟨533052842059825888389299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 355368561373217258926199 533052842059825888389299)
  ·
    refine ⟨799579263089738832583949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 533052842059825888389299 799579263089738832583949)
    ·
      refine ⟨299842223658652062218981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 799579263089738832583949 299842223658652062218981)
      ·
        refine ⟨56220416935997261666059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299842223658652062218981 56220416935997261666059)
        ·
          refine ⟨84330625403995892499089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56220416935997261666059 84330625403995892499089)
          ·
            refine ⟨63247969052996919374317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84330625403995892499089 63247969052996919374317)
            ·
              refine ⟨23717988394873844765369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63247969052996919374317 23717988394873844765369)
              ·
                refine ⟨17788491296155383574027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23717988394873844765369 17788491296155383574027)
                ·
                  refine ⟨26682736944233075361041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788491296155383574027 26682736944233075361041)
                  ·
                    refine ⟨20012052708174806520781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26682736944233075361041 20012052708174806520781)
                    ·
                      refine ⟨7504519765565552445293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20012052708174806520781 7504519765565552445293)
                      ·
                        rfl

theorem cell23_14615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_14615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14615 prefixEnd_14615 := by exact prefixLift 14615
  have htrace : WordTrace (prefixWord ++ tailWord_14615) baseStart_14615 baseEnd_14615 := by
    simpa [prefixWord, tailWord_14615, baseEnd_14615] using wordTrace_append hprefix tailTrace_14615
  have hstable : (prefixWord ++ tailWord_14615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14615).length < 2 ^ (prefixWord ++ tailWord_14615).sum := by decide
  have hdescent : baseEnd_14615 < baseStart_14615 := by decide
  rcases family_descends (prefixWord ++ tailWord_14615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14628 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_14628 : Nat := 118140960795 + 14628 * 2 ^ 59
def prefixEnd_14628 : Nat := 4983230072969 + 3 ^ 40 * 14628 * 2
def baseEnd_14628 : Nat := 7511195014074001582733

theorem tailTrace_14628 : CollatzResearch.WordTrace tailWord_14628 prefixEnd_14628 7511195014074001582733 := by
  unfold tailWord_14628
  simp only [CollatzResearch.WordTrace]
  refine ⟨266763495506364554306269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 355684660675152739075025 266763495506364554306269)
  ·
    refine ⟨100036310814886707864851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 266763495506364554306269 100036310814886707864851)
    ·
      refine ⟨150054466222330061797277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100036310814886707864851 150054466222330061797277)
      ·
        refine ⟨56270424833373773173979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150054466222330061797277 56270424833373773173979)
        ·
          refine ⟨84405637250060659760969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56270424833373773173979 84405637250060659760969)
          ·
            refine ⟨63304227937545494820727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84405637250060659760969 63304227937545494820727)
            ·
              refine ⟨94956341906318242231091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63304227937545494820727 94956341906318242231091)
              ·
                refine ⟨142434512859477363346637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94956341906318242231091 142434512859477363346637)
                ·
                  refine ⟨53412942322304011254989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142434512859477363346637 53412942322304011254989)
                  ·
                    refine ⟨20029853370864004220621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53412942322304011254989 20029853370864004220621)
                    ·
                      refine ⟨7511195014074001582733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20029853370864004220621 7511195014074001582733)
                      ·
                        rfl

theorem cell23_14628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_14628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14628 prefixEnd_14628 := by exact prefixLift 14628
  have htrace : WordTrace (prefixWord ++ tailWord_14628) baseStart_14628 baseEnd_14628 := by
    simpa [prefixWord, tailWord_14628, baseEnd_14628] using wordTrace_append hprefix tailTrace_14628
  have hstable : (prefixWord ++ tailWord_14628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14628).length < 2 ^ (prefixWord ++ tailWord_14628).sum := by decide
  have hdescent : baseEnd_14628 < baseStart_14628 := by decide
  rcases family_descends (prefixWord ++ tailWord_14628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14632 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_14632 : Nat := 118140960795 + 14632 * 2 ^ 59
def prefixEnd_14632 : Nat := 4983230072969 + 3 ^ 40 * 14632 * 2
def baseEnd_14632 : Nat := 7513248936691985932715

theorem tailTrace_14632 : CollatzResearch.WordTrace tailWord_14632 prefixEnd_14632 7513248936691985932715 := by
  unfold tailWord_14632
  simp only [CollatzResearch.WordTrace]
  refine ⟨266836441499118895879075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 355781921998825194505433 266836441499118895879075)
  ·
    refine ⟨400254662248678343818613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266836441499118895879075 400254662248678343818613)
    ·
      refine ⟨37523874585813594732995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 400254662248678343818613 37523874585813594732995)
      ·
        refine ⟨56285811878720392099493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37523874585813594732995 56285811878720392099493)
        ·
          refine ⟨10553589727260073518655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56285811878720392099493 10553589727260073518655)
          ·
            refine ⟨15830384590890110277983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553589727260073518655 15830384590890110277983)
            ·
              refine ⟨23745576886335165416975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15830384590890110277983 23745576886335165416975)
              ·
                refine ⟨35618365329502748125463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23745576886335165416975 35618365329502748125463)
                ·
                  refine ⟨53427547994254122188195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35618365329502748125463 53427547994254122188195)
                  ·
                    refine ⟨80141321991381183282293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53427547994254122188195 80141321991381183282293)
                    ·
                      refine ⟨7513248936691985932715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 80141321991381183282293 7513248936691985932715)
                      ·
                        rfl

theorem cell23_14632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_14632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14632 prefixEnd_14632 := by exact prefixLift 14632
  have htrace : WordTrace (prefixWord ++ tailWord_14632) baseStart_14632 baseEnd_14632 := by
    simpa [prefixWord, tailWord_14632, baseEnd_14632] using wordTrace_append hprefix tailTrace_14632
  have hstable : (prefixWord ++ tailWord_14632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14632).length < 2 ^ (prefixWord ++ tailWord_14632).sum := by decide
  have hdescent : baseEnd_14632 < baseStart_14632 := by decide
  rcases family_descends (prefixWord ++ tailWord_14632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14671 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_14671 : Nat := 118140960795 + 14671 * 2 ^ 59
def prefixEnd_14671 : Nat := 4983230072969 + 3 ^ 40 * 14671 * 2
def baseEnd_14671 : Nat := 7533274682217333345035

theorem tailTrace_14671 : CollatzResearch.WordTrace tailWord_14671 prefixEnd_14671 7533274682217333345035 := by
  unfold tailWord_14671
  simp only [CollatzResearch.WordTrace]
  refine ⟨535095329856947452427867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356730219904631634951911 535095329856947452427867)
  ·
    refine ⟨802642994785421178641801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535095329856947452427867 802642994785421178641801)
    ·
      refine ⟨601982246089065883981351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 802642994785421178641801 601982246089065883981351)
      ·
        refine ⟨902973369133598825972027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601982246089065883981351 902973369133598825972027)
        ·
          refine ⟨1354460053700398238958041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902973369133598825972027 1354460053700398238958041)
          ·
            refine ⟨1015845040275298679218531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354460053700398238958041 1015845040275298679218531)
            ·
              refine ⟨1523767560412948018827797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015845040275298679218531 1523767560412948018827797)
              ·
                refine ⟨71426604394356938382553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1523767560412948018827797 71426604394356938382553)
                ·
                  refine ⟨53569953295767703786915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71426604394356938382553 53569953295767703786915)
                  ·
                    refine ⟨80354929943651555680373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53569953295767703786915 80354929943651555680373)
                    ·
                      refine ⟨7533274682217333345035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 80354929943651555680373 7533274682217333345035)
                      ·
                        rfl

theorem cell23_14671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_14671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14671 prefixEnd_14671 := by exact prefixLift 14671
  have htrace : WordTrace (prefixWord ++ tailWord_14671) baseStart_14671 baseEnd_14671 := by
    simpa [prefixWord, tailWord_14671, baseEnd_14671] using wordTrace_append hprefix tailTrace_14671
  have hstable : (prefixWord ++ tailWord_14671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14671).length < 2 ^ (prefixWord ++ tailWord_14671).sum := by decide
  have hdescent : baseEnd_14671 < baseStart_14671 := by decide
  rcases family_descends (prefixWord ++ tailWord_14671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14681 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 4]
def baseStart_14681 : Nat := 118140960795 + 14681 * 2 ^ 59
def prefixEnd_14681 : Nat := 4983230072969 + 3 ^ 40 * 14681 * 2
def baseEnd_14681 : Nat := 7538409488762294219989

theorem tailTrace_14681 : CollatzResearch.WordTrace tailWord_14681 prefixEnd_14681 7538409488762294219989 := by
  unfold tailWord_14681
  simp only [CollatzResearch.WordTrace]
  refine ⟨535460059820719160291897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356973373213812773527931 535460059820719160291897)
  ·
    refine ⟨401595044865539370218923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535460059820719160291897 401595044865539370218923)
    ·
      refine ⟨602392567298309055328385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401595044865539370218923 602392567298309055328385)
      ·
        refine ⟨451794425473731791496289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602392567298309055328385 451794425473731791496289)
        ·
          refine ⟨338845819105298843622217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451794425473731791496289 338845819105298843622217)
          ·
            refine ⟨254134364328974132716663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338845819105298843622217 254134364328974132716663)
            ·
              refine ⟨381201546493461199074995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254134364328974132716663 381201546493461199074995)
              ·
                refine ⟨571802319740191798612493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381201546493461199074995 571802319740191798612493)
                ·
                  refine ⟨214425869902571924479685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571802319740191798612493 214425869902571924479685)
                  ·
                    refine ⟨40204850606732235839941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214425869902571924479685 40204850606732235839941)
                    ·
                      refine ⟨7538409488762294219989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 40204850606732235839941 7538409488762294219989)
                      ·
                        rfl

theorem cell23_14681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_14681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14681 prefixEnd_14681 := by exact prefixLift 14681
  have htrace : WordTrace (prefixWord ++ tailWord_14681) baseStart_14681 baseEnd_14681 := by
    simpa [prefixWord, tailWord_14681, baseEnd_14681] using wordTrace_append hprefix tailTrace_14681
  have hstable : (prefixWord ++ tailWord_14681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14681).length < 2 ^ (prefixWord ++ tailWord_14681).sum := by decide
  have hdescent : baseEnd_14681 < baseStart_14681 := by decide
  rcases family_descends (prefixWord ++ tailWord_14681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14691 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 9]
def baseStart_14691 : Nat := 118140960795 + 14691 * 2 ^ 59
def prefixEnd_14691 : Nat := 4983230072969 + 3 ^ 40 * 14691 * 2
def baseEnd_14691 : Nat := 838171588367472788327

theorem tailTrace_14691 : CollatzResearch.WordTrace tailWord_14691 prefixEnd_14691 838171588367472788327 := by
  unfold tailWord_14691
  simp only [CollatzResearch.WordTrace]
  refine ⟨535824789784490868155927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 357216526522993912103951 535824789784490868155927)
  ·
    refine ⟨803737184676736302233891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535824789784490868155927 803737184676736302233891)
    ·
      refine ⟨1205605777015104453350837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803737184676736302233891 1205605777015104453350837)
      ·
        refine ⟨113025541595166042501641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1205605777015104453350837 113025541595166042501641)
        ·
          refine ⟨84769156196374531876231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113025541595166042501641 84769156196374531876231)
          ·
            refine ⟨127153734294561797814347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84769156196374531876231 127153734294561797814347)
            ·
              refine ⟨190730601441842696721521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127153734294561797814347 190730601441842696721521)
              ·
                refine ⟨143047951081382022541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190730601441842696721521 143047951081382022541141)
                ·
                  refine ⟨838171588367472788327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 143047951081382022541141 838171588367472788327)
                  ·
                    rfl

theorem cell23_14691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 9].length) (baseStart_14691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14691 prefixEnd_14691 := by exact prefixLift 14691
  have htrace : WordTrace (prefixWord ++ tailWord_14691) baseStart_14691 baseEnd_14691 := by
    simpa [prefixWord, tailWord_14691, baseEnd_14691] using wordTrace_append hprefix tailTrace_14691
  have hstable : (prefixWord ++ tailWord_14691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14691).length < 2 ^ (prefixWord ++ tailWord_14691).sum := by decide
  have hdescent : baseEnd_14691 < baseStart_14691 := by decide
  rcases family_descends (prefixWord ++ tailWord_14691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_14778 : Nat := 118140960795 + 14778 * 2 ^ 59
def prefixEnd_14778 : Nat := 4983230072969 + 3 ^ 40 * 14778 * 2
def baseEnd_14778 : Nat := 7588217112248414707043

theorem tailTrace_14778 : CollatzResearch.WordTrace tailWord_14778 prefixEnd_14778 7588217112248414707043 := by
  unfold tailWord_14778
  simp only [CollatzResearch.WordTrace]
  refine ⟨134749485117326181643247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 359331960312869817715325 134749485117326181643247)
  ·
    refine ⟨202124227675989272464871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134749485117326181643247 202124227675989272464871)
    ·
      refine ⟨303186341513983908697307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202124227675989272464871 303186341513983908697307)
      ·
        refine ⟨454779512270975863045961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303186341513983908697307 454779512270975863045961)
        ·
          refine ⟨341084634203231897284471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454779512270975863045961 341084634203231897284471)
          ·
            refine ⟨511626951304847845926707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341084634203231897284471 511626951304847845926707)
            ·
              refine ⟨767440426957271768890061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511626951304847845926707 767440426957271768890061)
              ·
                refine ⟨287790160108976913333773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 767440426957271768890061 287790160108976913333773)
                ·
                  refine ⟨107921310040866342500165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287790160108976913333773 107921310040866342500165)
                  ·
                    refine ⟨20235245632662439218781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107921310040866342500165 20235245632662439218781)
                    ·
                      refine ⟨7588217112248414707043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20235245632662439218781 7588217112248414707043)
                      ·
                        rfl

theorem cell23_14778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_14778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14778 prefixEnd_14778 := by exact prefixLift 14778
  have htrace : WordTrace (prefixWord ++ tailWord_14778) baseStart_14778 baseEnd_14778 := by
    simpa [prefixWord, tailWord_14778, baseEnd_14778] using wordTrace_append hprefix tailTrace_14778
  have hstable : (prefixWord ++ tailWord_14778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14778).length < 2 ^ (prefixWord ++ tailWord_14778).sum := by decide
  have hdescent : baseEnd_14778 < baseStart_14778 := by decide
  rcases family_descends (prefixWord ++ tailWord_14778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14815 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 6]
def baseStart_14815 : Nat := 118140960795 + 14815 * 2 ^ 59
def prefixEnd_14815 : Nat := 4983230072969 + 3 ^ 40 * 14815 * 2
def baseEnd_14815 : Nat := 845246210718307771597

theorem tailTrace_14815 : CollatzResearch.WordTrace tailWord_14815 prefixEnd_14815 845246210718307771597 := by
  unfold tailWord_14815
  simp only [CollatzResearch.WordTrace]
  refine ⟨540347441335260045669899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 360231627556840030446599 540347441335260045669899)
  ·
    refine ⟨810521162002890068504849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540347441335260045669899 810521162002890068504849)
    ·
      refine ⟨607890871502167551378637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 810521162002890068504849 607890871502167551378637)
      ·
        refine ⟨227959076813312831766989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 607890871502167551378637 227959076813312831766989)
        ·
          refine ⟨85484653804992311912621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227959076813312831766989 85484653804992311912621)
          ·
            refine ⟨32056745176872116967233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85484653804992311912621 32056745176872116967233)
            ·
              refine ⟨24042558882654087725425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32056745176872116967233 24042558882654087725425)
              ·
                refine ⟨18031919161990565794069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24042558882654087725425 18031919161990565794069)
                ·
                  refine ⟨845246210718307771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18031919161990565794069 845246210718307771597)
                  ·
                    rfl

theorem cell23_14815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 6].length) (baseStart_14815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14815 prefixEnd_14815 := by exact prefixLift 14815
  have htrace : WordTrace (prefixWord ++ tailWord_14815) baseStart_14815 baseEnd_14815 := by
    simpa [prefixWord, tailWord_14815, baseEnd_14815] using wordTrace_append hprefix tailTrace_14815
  have hstable : (prefixWord ++ tailWord_14815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14815).length < 2 ^ (prefixWord ++ tailWord_14815).sum := by decide
  have hdescent : baseEnd_14815 < baseStart_14815 := by decide
  rcases family_descends (prefixWord ++ tailWord_14815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14819 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 1, 4]
def baseStart_14819 : Nat := 118140960795 + 14819 * 2 ^ 59
def prefixEnd_14819 : Nat := 4983230072969 + 3 ^ 40 * 14819 * 2
def baseEnd_14819 : Nat := 2536423273027584764785

theorem tailTrace_14819 : CollatzResearch.WordTrace tailWord_14819 prefixEnd_14819 2536423273027584764785 := by
  unfold tailWord_14819
  simp only [CollatzResearch.WordTrace]
  refine ⟨540493333320768728815511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 360328888880512485877007 540493333320768728815511)
  ·
    refine ⟨810739999981153093223267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 540493333320768728815511 810739999981153093223267)
    ·
      refine ⟨1216109999971729639834901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 810739999981153093223267 1216109999971729639834901)
      ·
        refine ⟨57005156248674826867261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1216109999971729639834901 57005156248674826867261)
        ·
          refine ⟨21376933593253060075223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57005156248674826867261 21376933593253060075223)
          ·
            refine ⟨32065400389879590112835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21376933593253060075223 32065400389879590112835)
            ·
              refine ⟨48098100584819385169253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32065400389879590112835 48098100584819385169253)
              ·
                refine ⟨9018393859653634719235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48098100584819385169253 9018393859653634719235)
                ·
                  refine ⟨13527590789480452078853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9018393859653634719235 13527590789480452078853)
                  ·
                    refine ⟨2536423273027584764785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13527590789480452078853 2536423273027584764785)
                    ·
                      rfl

theorem cell23_14819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 4].length) (baseStart_14819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14819 prefixEnd_14819 := by exact prefixLift 14819
  have htrace : WordTrace (prefixWord ++ tailWord_14819) baseStart_14819 baseEnd_14819 := by
    simpa [prefixWord, tailWord_14819, baseEnd_14819] using wordTrace_append hprefix tailTrace_14819
  have hstable : (prefixWord ++ tailWord_14819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14819).length < 2 ^ (prefixWord ++ tailWord_14819).sum := by decide
  have hdescent : baseEnd_14819 < baseStart_14819 := by decide
  rcases family_descends (prefixWord ++ tailWord_14819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14828 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_14828 : Nat := 118140960795 + 14828 * 2 ^ 59
def prefixEnd_14828 : Nat := 4983230072969 + 3 ^ 40 * 14828 * 2
def baseEnd_14828 : Nat := 2537963714991073027271

theorem tailTrace_14828 : CollatzResearch.WordTrace tailWord_14828 prefixEnd_14828 2537963714991073027271 := by
  unfold tailWord_14828
  simp only [CollatzResearch.WordTrace]
  refine ⟨270410795144081632946569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 360547726858775510595425 270410795144081632946569)
  ·
    refine ⟨202808096358061224709927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270410795144081632946569 202808096358061224709927)
    ·
      refine ⟨304212144537091837064891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202808096358061224709927 304212144537091837064891)
      ·
        refine ⟨456318216805637755597337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304212144537091837064891 456318216805637755597337)
        ·
          refine ⟨342238662604228316698003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456318216805637755597337 342238662604228316698003)
          ·
            refine ⟨513357993906342475047005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342238662604228316698003 513357993906342475047005)
            ·
              refine ⟨192509247714878428142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 513357993906342475047005 192509247714878428142627)
              ·
                refine ⟨288763871572317642213941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192509247714878428142627 288763871572317642213941)
                ·
                  refine ⟨27071612959904778957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288763871572317642213941 27071612959904778957557)
                  ·
                    refine ⟨2537963714991073027271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27071612959904778957557 2537963714991073027271)
                    ·
                      rfl

theorem cell23_14828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_14828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14828 prefixEnd_14828 := by exact prefixLift 14828
  have htrace : WordTrace (prefixWord ++ tailWord_14828) baseStart_14828 baseEnd_14828 := by
    simpa [prefixWord, tailWord_14828, baseEnd_14828] using wordTrace_append hprefix tailTrace_14828
  have hstable : (prefixWord ++ tailWord_14828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14828).length < 2 ^ (prefixWord ++ tailWord_14828).sum := by decide
  have hdescent : baseEnd_14828 < baseStart_14828 := by decide
  rcases family_descends (prefixWord ++ tailWord_14828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14835 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 5, 2]
def baseStart_14835 : Nat := 118140960795 + 14835 * 2 ^ 59
def prefixEnd_14835 : Nat := 4983230072969 + 3 ^ 40 * 14835 * 2
def baseEnd_14835 : Nat := 7617485509554691694281

theorem tailTrace_14835 : CollatzResearch.WordTrace tailWord_14835 prefixEnd_14835 7617485509554691694281 := by
  unfold tailWord_14835
  simp only [CollatzResearch.WordTrace]
  refine ⟨541076901262803461397959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 360717934175202307598639 541076901262803461397959)
  ·
    refine ⟨811615351894205192096939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541076901262803461397959 811615351894205192096939)
    ·
      refine ⟨1217423027841307788145409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811615351894205192096939 1217423027841307788145409)
      ·
        refine ⟨913067270880980841109057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217423027841307788145409 913067270880980841109057)
        ·
          refine ⟨684800453160735630831793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913067270880980841109057 684800453160735630831793)
          ·
            refine ⟨513600339870551723123845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 684800453160735630831793 513600339870551723123845)
            ·
              refine ⟨96300063725728448085721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513600339870551723123845 96300063725728448085721)
              ·
                refine ⟨72225047794296336064291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96300063725728448085721 72225047794296336064291)
                ·
                  refine ⟨108337571691444504096437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72225047794296336064291 108337571691444504096437)
                  ·
                    refine ⟨10156647346072922259041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108337571691444504096437 10156647346072922259041)
                    ·
                      refine ⟨7617485509554691694281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10156647346072922259041 7617485509554691694281)
                      ·
                        rfl

theorem cell23_14835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 5, 2].length) (baseStart_14835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14835 prefixEnd_14835 := by exact prefixLift 14835
  have htrace : WordTrace (prefixWord ++ tailWord_14835) baseStart_14835 baseEnd_14835 := by
    simpa [prefixWord, tailWord_14835, baseEnd_14835] using wordTrace_append hprefix tailTrace_14835
  have hstable : (prefixWord ++ tailWord_14835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14835).length < 2 ^ (prefixWord ++ tailWord_14835).sum := by decide
  have hdescent : baseEnd_14835 < baseStart_14835 := by decide
  rcases family_descends (prefixWord ++ tailWord_14835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14845 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_14845 : Nat := 118140960795 + 14845 * 2 ^ 59
def prefixEnd_14845 : Nat := 4983230072969 + 3 ^ 40 * 14845 * 2
def baseEnd_14845 : Nat := 2540873438699884189745

theorem tailTrace_14845 : CollatzResearch.WordTrace tailWord_14845 prefixEnd_14845 2540873438699884189745 := by
  unfold tailWord_14845
  simp only [CollatzResearch.WordTrace]
  refine ⟨541441631226575169261989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 360961087484383446174659 541441631226575169261989)
  ·
    refine ⟨101520305854982844236623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 541441631226575169261989 101520305854982844236623)
    ·
      refine ⟨152280458782474266354935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101520305854982844236623 152280458782474266354935)
      ·
        refine ⟨228420688173711399532403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152280458782474266354935 228420688173711399532403)
        ·
          refine ⟨342631032260567099298605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228420688173711399532403 342631032260567099298605)
          ·
            refine ⟨128486637097712662236977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342631032260567099298605 128486637097712662236977)
            ·
              refine ⟨96364977823284496677733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128486637097712662236977 96364977823284496677733)
              ·
                refine ⟨18068433341865843127075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96364977823284496677733 18068433341865843127075)
                ·
                  refine ⟨27102650012798764690613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18068433341865843127075 27102650012798764690613)
                  ·
                    refine ⟨2540873438699884189745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27102650012798764690613 2540873438699884189745)
                    ·
                      rfl

theorem cell23_14845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_14845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14845 prefixEnd_14845 := by exact prefixLift 14845
  have htrace : WordTrace (prefixWord ++ tailWord_14845) baseStart_14845 baseEnd_14845 := by
    simpa [prefixWord, tailWord_14845, baseEnd_14845] using wordTrace_append hprefix tailTrace_14845
  have hstable : (prefixWord ++ tailWord_14845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14845).length < 2 ^ (prefixWord ++ tailWord_14845).sum := by decide
  have hdescent : baseEnd_14845 < baseStart_14845 := by decide
  rcases family_descends (prefixWord ++ tailWord_14845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14859 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 1, 1, 3]
def baseStart_14859 : Nat := 118140960795 + 14859 * 2 ^ 59
def prefixEnd_14859 : Nat := 4983230072969 + 3 ^ 40 * 14859 * 2
def baseEnd_14859 : Nat := 7629809045262597794171

theorem tailTrace_14859 : CollatzResearch.WordTrace tailWord_14859 prefixEnd_14859 7629809045262597794171 := by
  unfold tailWord_14859
  simp only [CollatzResearch.WordTrace]
  refine ⟨541952253175855560271631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 361301502117237040181087 541952253175855560271631)
  ·
    refine ⟨812928379763783340407447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541952253175855560271631 812928379763783340407447)
    ·
      refine ⟨1219392569645675010611171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812928379763783340407447 1219392569645675010611171)
      ·
        refine ⟨1829088854468512515916757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219392569645675010611171 1829088854468512515916757)
        ·
          refine ⟨42869270026605762091799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1829088854468512515916757 42869270026605762091799)
          ·
            refine ⟨64303905039908643137699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42869270026605762091799 64303905039908643137699)
            ·
              refine ⟨96455857559862964706549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64303905039908643137699 96455857559862964706549)
              ·
                refine ⟨9042736646237152941239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96455857559862964706549 9042736646237152941239)
                ·
                  refine ⟨13564104969355729411859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9042736646237152941239 13564104969355729411859)
                  ·
                    refine ⟨20346157454033594117789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13564104969355729411859 20346157454033594117789)
                    ·
                      refine ⟨7629809045262597794171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20346157454033594117789 7629809045262597794171)
                      ·
                        rfl

theorem cell23_14859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 1, 3].length) (baseStart_14859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14859 prefixEnd_14859 := by exact prefixLift 14859
  have htrace : WordTrace (prefixWord ++ tailWord_14859) baseStart_14859 baseEnd_14859 := by
    simpa [prefixWord, tailWord_14859, baseEnd_14859] using wordTrace_append hprefix tailTrace_14859
  have hstable : (prefixWord ++ tailWord_14859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14859).length < 2 ^ (prefixWord ++ tailWord_14859).sum := by decide
  have hdescent : baseEnd_14859 < baseStart_14859 := by decide
  rcases family_descends (prefixWord ++ tailWord_14859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14862 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_14862 : Nat := 118140960795 + 14862 * 2 ^ 59
def prefixEnd_14862 : Nat := 4983230072969 + 3 ^ 40 * 14862 * 2
def baseEnd_14862 : Nat := 2543783162408695352219

theorem tailTrace_14862 : CollatzResearch.WordTrace tailWord_14862 prefixEnd_14862 2543783162408695352219 := by
  unfold tailWord_14862
  simp only [CollatzResearch.WordTrace]
  refine ⟨67757709020623384078855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 361374448109991381753893 67757709020623384078855)
  ·
    refine ⟨101636563530935076118283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67757709020623384078855 101636563530935076118283)
    ·
      refine ⟨152454845296402614177425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101636563530935076118283 152454845296402614177425)
      ·
        refine ⟨114341133972301960633069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152454845296402614177425 114341133972301960633069)
        ·
          refine ⟨42877925239613235237401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114341133972301960633069 42877925239613235237401)
          ·
            refine ⟨32158443929709926428051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42877925239613235237401 32158443929709926428051)
            ·
              refine ⟨48237665894564889642077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32158443929709926428051 48237665894564889642077)
              ·
                refine ⟨18089124710461833615779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48237665894564889642077 18089124710461833615779)
                ·
                  refine ⟨27133687065692750423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18089124710461833615779 27133687065692750423669)
                  ·
                    refine ⟨2543783162408695352219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27133687065692750423669 2543783162408695352219)
                    ·
                      rfl

theorem cell23_14862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_14862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14862 prefixEnd_14862 := by exact prefixLift 14862
  have htrace : WordTrace (prefixWord ++ tailWord_14862) baseStart_14862 baseEnd_14862 := by
    simpa [prefixWord, tailWord_14862, baseEnd_14862] using wordTrace_append hprefix tailTrace_14862
  have hstable : (prefixWord ++ tailWord_14862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14862).length < 2 ^ (prefixWord ++ tailWord_14862).sum := by decide
  have hdescent : baseEnd_14862 < baseStart_14862 := by decide
  rcases family_descends (prefixWord ++ tailWord_14862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14885 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_14885 : Nat := 118140960795 + 14885 * 2 ^ 59
def prefixEnd_14885 : Nat := 4983230072969 + 3 ^ 40 * 14885 * 2
def baseEnd_14885 : Nat := 7643159542279496069051

theorem tailTrace_14885 : CollatzResearch.WordTrace tailWord_14885 prefixEnd_14885 7643159542279496069051 := by
  unfold tailWord_14885
  simp only [CollatzResearch.WordTrace]
  refine ⟨542900551081662000718109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 361933700721108000478739 542900551081662000718109)
  ·
    refine ⟨203587706655623250269291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 542900551081662000718109 203587706655623250269291)
    ·
      refine ⟨305381559983434875403937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203587706655623250269291 305381559983434875403937)
      ·
        refine ⟨229036169987576156552953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305381559983434875403937 229036169987576156552953)
        ·
          refine ⟨171777127490682117414715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229036169987576156552953 171777127490682117414715)
          ·
            refine ⟨257665691236023176122073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171777127490682117414715 257665691236023176122073)
            ·
              refine ⟨193249268427017382091555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257665691236023176122073 193249268427017382091555)
              ·
                refine ⟨289873902640526073137333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193249268427017382091555 289873902640526073137333)
                ·
                  refine ⟨27175678372549319356625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289873902640526073137333 27175678372549319356625)
                  ·
                    refine ⟨20381758779411989517469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27175678372549319356625 20381758779411989517469)
                    ·
                      refine ⟨7643159542279496069051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20381758779411989517469 7643159542279496069051)
                      ·
                        rfl

theorem cell23_14885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_14885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14885 prefixEnd_14885 := by exact prefixLift 14885
  have htrace : WordTrace (prefixWord ++ tailWord_14885) baseStart_14885 baseEnd_14885 := by
    simpa [prefixWord, tailWord_14885, baseEnd_14885] using wordTrace_append hprefix tailTrace_14885
  have hstable : (prefixWord ++ tailWord_14885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14885).length < 2 ^ (prefixWord ++ tailWord_14885).sum := by decide
  have hdescent : baseEnd_14885 < baseStart_14885 := by decide
  rcases family_descends (prefixWord ++ tailWord_14885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14910 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_14910 : Nat := 118140960795 + 14910 * 2 ^ 59
def prefixEnd_14910 : Nat := 4983230072969 + 3 ^ 40 * 14910 * 2
def baseEnd_14910 : Nat := 7655996558641898256437

theorem tailTrace_14910 : CollatzResearch.WordTrace tailWord_14910 prefixEnd_14910 7655996558641898256437 := by
  unfold tailWord_14910
  simp only [CollatzResearch.WordTrace]
  refine ⟨67976546998886408797273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 362541583994060846918789 67976546998886408797273)
  ·
    refine ⟨50982410249164806597955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67976546998886408797273 50982410249164806597955)
    ·
      refine ⟨76473615373747209896933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50982410249164806597955 76473615373747209896933)
      ·
        refine ⟨14338802882577601855675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76473615373747209896933 14338802882577601855675)
        ·
          refine ⟨21508204323866402783513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14338802882577601855675 21508204323866402783513)
          ·
            refine ⟨16131153242899802087635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21508204323866402783513 16131153242899802087635)
            ·
              refine ⟨24196729864349703131453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16131153242899802087635 24196729864349703131453)
              ·
                refine ⟨9073773699131138674295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24196729864349703131453 9073773699131138674295)
                ·
                  refine ⟨13610660548696708011443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9073773699131138674295 13610660548696708011443)
                  ·
                    refine ⟨20415990823045062017165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13610660548696708011443 20415990823045062017165)
                    ·
                      refine ⟨7655996558641898256437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20415990823045062017165 7655996558641898256437)
                      ·
                        rfl

theorem cell23_14910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_14910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14910 prefixEnd_14910 := by exact prefixLift 14910
  have htrace : WordTrace (prefixWord ++ tailWord_14910) baseStart_14910 baseEnd_14910 := by
    simpa [prefixWord, tailWord_14910, baseEnd_14910] using wordTrace_append hprefix tailTrace_14910
  have hstable : (prefixWord ++ tailWord_14910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14910).length < 2 ^ (prefixWord ++ tailWord_14910).sum := by decide
  have hdescent : baseEnd_14910 < baseStart_14910 := by decide
  rcases family_descends (prefixWord ++ tailWord_14910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14915 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3]
def baseStart_14915 : Nat := 118140960795 + 14915 * 2 ^ 59
def prefixEnd_14915 : Nat := 4983230072969 + 3 ^ 40 * 14915 * 2
def baseEnd_14915 : Nat := 7658563961914378693913

theorem tailTrace_14915 : CollatzResearch.WordTrace tailWord_14915 prefixEnd_14915 7658563961914378693913 := by
  unfold tailWord_14915
  simp only [CollatzResearch.WordTrace]
  refine ⟨543994740972977124310199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 362663160648651416206799 543994740972977124310199)
  ·
    refine ⟨815992111459465686465299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543994740972977124310199 815992111459465686465299)
    ·
      refine ⟨1223988167189198529697949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815992111459465686465299 1223988167189198529697949)
      ·
        refine ⟨458995562695949448636731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1223988167189198529697949 458995562695949448636731)
        ·
          refine ⟨688493344043924172955097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458995562695949448636731 688493344043924172955097)
          ·
            refine ⟨516370008032943129716323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 688493344043924172955097 516370008032943129716323)
            ·
              refine ⟨774555012049414694574485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516370008032943129716323 774555012049414694574485)
              ·
                refine ⟨36307266189816313808179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 774555012049414694574485 36307266189816313808179)
                ·
                  refine ⟨54460899284724470712269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36307266189816313808179 54460899284724470712269)
                  ·
                    refine ⟨20422837231771676517101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54460899284724470712269 20422837231771676517101)
                    ·
                      refine ⟨7658563961914378693913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20422837231771676517101 7658563961914378693913)
                      ·
                        rfl

theorem cell23_14915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_14915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14915 prefixEnd_14915 := by exact prefixLift 14915
  have htrace : WordTrace (prefixWord ++ tailWord_14915) baseStart_14915 baseEnd_14915 := by
    simpa [prefixWord, tailWord_14915, baseEnd_14915] using wordTrace_append hprefix tailTrace_14915
  have hstable : (prefixWord ++ tailWord_14915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14915).length < 2 ^ (prefixWord ++ tailWord_14915).sum := by decide
  have hdescent : baseEnd_14915 < baseStart_14915 := by decide
  rcases family_descends (prefixWord ++ tailWord_14915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14959 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 1, 3, 2]
def baseStart_14959 : Nat := 118140960795 + 14959 * 2 ^ 59
def prefixEnd_14959 : Nat := 4983230072969 + 3 ^ 40 * 14959 * 2
def baseEnd_14959 : Nat := 7681157110712206543711

theorem tailTrace_14959 : CollatzResearch.WordTrace tailWord_14959 prefixEnd_14959 7681157110712206543711 := by
  unfold tailWord_14959
  simp only [CollatzResearch.WordTrace]
  refine ⟨545599552813572638911931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 363733035209048425941287 545599552813572638911931)
  ·
    refine ⟨818399329220358958367897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545599552813572638911931 818399329220358958367897)
    ·
      refine ⟨613799496915269218775923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 818399329220358958367897 613799496915269218775923)
      ·
        refine ⟨920699245372903828163885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613799496915269218775923 920699245372903828163885)
        ·
          refine ⟨345262217014838935561457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920699245372903828163885 345262217014838935561457)
          ·
            refine ⟨258946662761129201671093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345262217014838935561457 258946662761129201671093)
            ·
              refine ⟨24276249633855862656665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 258946662761129201671093 24276249633855862656665)
              ·
                refine ⟨18207187225391896992499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24276249633855862656665 18207187225391896992499)
                ·
                  refine ⟨27310780838087845488749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18207187225391896992499 27310780838087845488749)
                  ·
                    refine ⟨10241542814282942058281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27310780838087845488749 10241542814282942058281)
                    ·
                      refine ⟨7681157110712206543711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10241542814282942058281 7681157110712206543711)
                      ·
                        rfl

theorem cell23_14959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3, 2].length) (baseStart_14959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14959 prefixEnd_14959 := by exact prefixLift 14959
  have htrace : WordTrace (prefixWord ++ tailWord_14959) baseStart_14959 baseEnd_14959 := by
    simpa [prefixWord, tailWord_14959, baseEnd_14959] using wordTrace_append hprefix tailTrace_14959
  have hstable : (prefixWord ++ tailWord_14959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14959).length < 2 ^ (prefixWord ++ tailWord_14959).sum := by decide
  have hdescent : baseEnd_14959 < baseStart_14959 := by decide
  rcases family_descends (prefixWord ++ tailWord_14959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14972 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_14972 : Nat := 118140960795 + 14972 * 2 ^ 59
def prefixEnd_14972 : Nat := 4983230072969 + 3 ^ 40 * 14972 * 2
def baseEnd_14972 : Nat := 7687832359220655681151

theorem tailTrace_14972 : CollatzResearch.WordTrace tailWord_14972 prefixEnd_14972 7687832359220655681151 := by
  unfold tailWord_14972
  simp only [CollatzResearch.WordTrace]
  refine ⟨273036850883237929567585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 364049134510983906090113 273036850883237929567585)
  ·
    refine ⟨204777638162428447175689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273036850883237929567585 204777638162428447175689)
    ·
      refine ⟨153583228621821335381767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204777638162428447175689 153583228621821335381767)
      ·
        refine ⟨230374842932732003072651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153583228621821335381767 230374842932732003072651)
        ·
          refine ⟨345562264399098004608977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230374842932732003072651 345562264399098004608977)
          ·
            refine ⟨259171698299323503456733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345562264399098004608977 259171698299323503456733)
            ·
              refine ⟨97189386862246313796275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259171698299323503456733 97189386862246313796275)
              ·
                refine ⟨145784080293369470694413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97189386862246313796275 145784080293369470694413)
                ·
                  refine ⟨54669030110013551510405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145784080293369470694413 54669030110013551510405)
                  ·
                    refine ⟨10250443145627540908201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54669030110013551510405 10250443145627540908201)
                    ·
                      refine ⟨7687832359220655681151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10250443145627540908201 7687832359220655681151)
                      ·
                        rfl

theorem cell23_14972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_14972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14972 prefixEnd_14972 := by exact prefixLift 14972
  have htrace : WordTrace (prefixWord ++ tailWord_14972) baseStart_14972 baseEnd_14972 := by
    simpa [prefixWord, tailWord_14972, baseEnd_14972] using wordTrace_append hprefix tailTrace_14972
  have hstable : (prefixWord ++ tailWord_14972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14972).length < 2 ^ (prefixWord ++ tailWord_14972).sum := by decide
  have hdescent : baseEnd_14972 < baseStart_14972 := by decide
  rcases family_descends (prefixWord ++ tailWord_14972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14976 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2]
def baseStart_14976 : Nat := 118140960795 + 14976 * 2 ^ 59
def prefixEnd_14976 : Nat := 4983230072969 + 3 ^ 40 * 14976 * 2
def baseEnd_14976 : Nat := 7689886281838640031133

theorem tailTrace_14976 : CollatzResearch.WordTrace tailWord_14976 prefixEnd_14976 7689886281838640031133 := by
  unfold tailWord_14976
  simp only [CollatzResearch.WordTrace]
  refine ⟨273109796875992271140391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 364146395834656361520521 273109796875992271140391)
  ·
    refine ⟨409664695313988406710587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273109796875992271140391 409664695313988406710587)
    ·
      refine ⟨614497042970982610065881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409664695313988406710587 614497042970982610065881)
      ·
        refine ⟨460872782228236957549411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614497042970982610065881 460872782228236957549411)
        ·
          refine ⟨691309173342355436324117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460872782228236957549411 691309173342355436324117)
          ·
            refine ⟨32405117500422911077693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 691309173342355436324117 32405117500422911077693)
            ·
              refine ⟨12151919062658591654135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32405117500422911077693 12151919062658591654135)
              ·
                refine ⟨18227878593987887481203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12151919062658591654135 18227878593987887481203)
                ·
                  refine ⟨27341817890981831221805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18227878593987887481203 27341817890981831221805)
                  ·
                    refine ⟨10253181709118186708177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27341817890981831221805 10253181709118186708177)
                    ·
                      refine ⟨7689886281838640031133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10253181709118186708177 7689886281838640031133)
                      ·
                        rfl

theorem cell23_14976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_14976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14976 prefixEnd_14976 := by exact prefixLift 14976
  have htrace : WordTrace (prefixWord ++ tailWord_14976) baseStart_14976 baseEnd_14976 := by
    simpa [prefixWord, tailWord_14976, baseEnd_14976] using wordTrace_append hprefix tailTrace_14976
  have hstable : (prefixWord ++ tailWord_14976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14976).length < 2 ^ (prefixWord ++ tailWord_14976).sum := by decide
  have hdescent : baseEnd_14976 < baseStart_14976 := by decide
  rcases family_descends (prefixWord ++ tailWord_14976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14985 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 4]
def baseStart_14985 : Nat := 118140960795 + 14985 * 2 ^ 59
def prefixEnd_14985 : Nat := 4983230072969 + 3 ^ 40 * 14985 * 2
def baseEnd_14985 : Nat := 7694507607729104818591

theorem tailTrace_14985 : CollatzResearch.WordTrace tailWord_14985 prefixEnd_14985 7694507607729104818591 := by
  unfold tailWord_14985
  simp only [CollatzResearch.WordTrace]
  refine ⟨546547850719379079358409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 364365233812919386238939 546547850719379079358409)
  ·
    refine ⟨409910888039534309518807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 546547850719379079358409 409910888039534309518807)
    ·
      refine ⟨614866332059301464278211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409910888039534309518807 614866332059301464278211)
      ·
        refine ⟨922299498088952196417317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614866332059301464278211 922299498088952196417317)
        ·
          refine ⟨172931155891678536828247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 922299498088952196417317 172931155891678536828247)
          ·
            refine ⟨259396733837517805242371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172931155891678536828247 259396733837517805242371)
            ·
              refine ⟨389095100756276707863557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259396733837517805242371 389095100756276707863557)
              ·
                refine ⟨72955331391801882724417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389095100756276707863557 72955331391801882724417)
                ·
                  refine ⟨54716498543851412043313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72955331391801882724417 54716498543851412043313)
                  ·
                    refine ⟨41037373907888559032485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54716498543851412043313 41037373907888559032485)
                    ·
                      refine ⟨7694507607729104818591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 41037373907888559032485 7694507607729104818591)
                      ·
                        rfl

theorem cell23_14985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_14985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_14985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_14985 prefixEnd_14985 := by exact prefixLift 14985
  have htrace : WordTrace (prefixWord ++ tailWord_14985) baseStart_14985 baseEnd_14985 := by
    simpa [prefixWord, tailWord_14985, baseEnd_14985] using wordTrace_append hprefix tailTrace_14985
  have hstable : (prefixWord ++ tailWord_14985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14985).length < 2 ^ (prefixWord ++ tailWord_14985).sum := by decide
  have hdescent : baseEnd_14985 < baseStart_14985 := by decide
  rcases family_descends (prefixWord ++ tailWord_14985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15006 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_15006 : Nat := 118140960795 + 15006 * 2 ^ 59
def prefixEnd_15006 : Nat := 4983230072969 + 3 ^ 40 * 15006 * 2
def baseEnd_15006 : Nat := 7705290701473522655995

theorem tailTrace_15006 : CollatzResearch.WordTrace tailWord_15006 prefixEnd_15006 7705290701473522655995 := by
  unfold tailWord_15006
  simp only [CollatzResearch.WordTrace]
  refine ⟨68414222955412458234109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 364875855762199777248581 68414222955412458234109)
  ·
    refine ⟨25655333608279671837791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68414222955412458234109 25655333608279671837791)
    ·
      refine ⟨38483000412419507756687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25655333608279671837791 38483000412419507756687)
      ·
        refine ⟨57724500618629261635031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38483000412419507756687 57724500618629261635031)
        ·
          refine ⟨86586750927943892452547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57724500618629261635031 86586750927943892452547)
          ·
            refine ⟨129880126391915838678821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86586750927943892452547 129880126391915838678821)
            ·
              refine ⟨24352523698484219752279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129880126391915838678821 24352523698484219752279)
              ·
                refine ⟨36528785547726329628419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24352523698484219752279 36528785547726329628419)
                ·
                  refine ⟨54793178321589494442629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36528785547726329628419 54793178321589494442629)
                  ·
                    refine ⟨10273720935298030207993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54793178321589494442629 10273720935298030207993)
                    ·
                      refine ⟨7705290701473522655995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10273720935298030207993 7705290701473522655995)
                      ·
                        rfl

theorem cell23_15006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_15006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15006 prefixEnd_15006 := by exact prefixLift 15006
  have htrace : WordTrace (prefixWord ++ tailWord_15006) baseStart_15006 baseEnd_15006 := by
    simpa [prefixWord, tailWord_15006, baseEnd_15006] using wordTrace_append hprefix tailTrace_15006
  have hstable : (prefixWord ++ tailWord_15006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15006).length < 2 ^ (prefixWord ++ tailWord_15006).sum := by decide
  have hdescent : baseEnd_15006 < baseStart_15006 := by decide
  rcases family_descends (prefixWord ++ tailWord_15006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15029 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 5]
def baseStart_15029 : Nat := 118140960795 + 15029 * 2 ^ 59
def prefixEnd_15029 : Nat := 4983230072969 + 3 ^ 40 * 15029 * 2
def baseEnd_15029 : Nat := 857455639614103629821

theorem tailTrace_15029 : CollatzResearch.WordTrace tailWord_15029 prefixEnd_15029 857455639614103629821 := by
  unfold tailWord_15029
  simp only [CollatzResearch.WordTrace]
  refine ⟨548152662559974593960141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 365435108373316395973427 548152662559974593960141)
  ·
    refine ⟨205557248459990472735053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 548152662559974593960141 205557248459990472735053)
    ·
      refine ⟨77083968172496427275645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205557248459990472735053 77083968172496427275645)
      ·
        refine ⟨28906488064686160228367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77083968172496427275645 28906488064686160228367)
        ·
          refine ⟨43359732097029240342551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906488064686160228367 43359732097029240342551)
          ·
            refine ⟨65039598145543860513827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43359732097029240342551 65039598145543860513827)
            ·
              refine ⟨97559397218315790770741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65039598145543860513827 97559397218315790770741)
              ·
                refine ⟨9146193489217105384757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97559397218315790770741 9146193489217105384757)
                ·
                  refine ⟨857455639614103629821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9146193489217105384757 857455639614103629821)
                  ·
                    rfl

theorem cell23_15029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_15029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15029 prefixEnd_15029 := by exact prefixLift 15029
  have htrace : WordTrace (prefixWord ++ tailWord_15029) baseStart_15029 baseEnd_15029 := by
    simpa [prefixWord, tailWord_15029, baseEnd_15029] using wordTrace_append hprefix tailTrace_15029
  have hstable : (prefixWord ++ tailWord_15029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15029).length < 2 ^ (prefixWord ++ tailWord_15029).sum := by decide
  have hdescent : baseEnd_15029 < baseStart_15029 := by decide
  rcases family_descends (prefixWord ++ tailWord_15029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15045 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_15045 : Nat := 118140960795 + 15045 * 2 ^ 59
def prefixEnd_15045 : Nat := 4983230072969 + 3 ^ 40 * 15045 * 2
def baseEnd_15045 : Nat := 7725316446998870068315

theorem tailTrace_15045 : CollatzResearch.WordTrace tailWord_15045 prefixEnd_15045 7725316446998870068315 := by
  unfold tailWord_15045
  simp only [CollatzResearch.WordTrace]
  refine ⟨548736230502009326542589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 365824153668006217695059 548736230502009326542589)
  ·
    refine ⟨205776086438253497453471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 548736230502009326542589 205776086438253497453471)
    ·
      refine ⟨308664129657380246180207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205776086438253497453471 308664129657380246180207)
      ·
        refine ⟨462996194486070369270311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308664129657380246180207 462996194486070369270311)
        ·
          refine ⟨694494291729105553905467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462996194486070369270311 694494291729105553905467)
          ·
            refine ⟨1041741437593658330858201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694494291729105553905467 1041741437593658330858201)
            ·
              refine ⟨781306078195243748143651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041741437593658330858201 781306078195243748143651)
              ·
                refine ⟨1171959117292865622215477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 781306078195243748143651 1171959117292865622215477)
                ·
                  refine ⟨109871167246206152082701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1171959117292865622215477 109871167246206152082701)
                  ·
                    refine ⟨41201687717327307031013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109871167246206152082701 41201687717327307031013)
                    ·
                      refine ⟨7725316446998870068315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 41201687717327307031013 7725316446998870068315)
                      ·
                        rfl

theorem cell23_15045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_15045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15045 prefixEnd_15045 := by exact prefixLift 15045
  have htrace : WordTrace (prefixWord ++ tailWord_15045) baseStart_15045 baseEnd_15045 := by
    simpa [prefixWord, tailWord_15045, baseEnd_15045] using wordTrace_append hprefix tailTrace_15045
  have hstable : (prefixWord ++ tailWord_15045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15045).length < 2 ^ (prefixWord ++ tailWord_15045).sum := by decide
  have hdescent : baseEnd_15045 < baseStart_15045 := by decide
  rcases family_descends (prefixWord ++ tailWord_15045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15093 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_15093 : Nat := 118140960795 + 15093 * 2 ^ 59
def prefixEnd_15093 : Nat := 4983230072969 + 3 ^ 40 * 15093 * 2
def baseEnd_15093 : Nat := 2583321172804894089365

theorem tailTrace_15093 : CollatzResearch.WordTrace tailWord_15093 prefixEnd_15093 2583321172804894089365 := by
  unfold tailWord_15093
  simp only [CollatzResearch.WordTrace]
  refine ⟨550486934328113524289933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 366991289552075682859955 550486934328113524289933)
  ·
    refine ⟨206432600373042571608725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 550486934328113524289933 206432600373042571608725)
    ·
      refine ⟨9676528142486370544159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 206432600373042571608725 9676528142486370544159)
      ·
        refine ⟨14514792213729555816239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9676528142486370544159 14514792213729555816239)
        ·
          refine ⟨21772188320594333724359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14514792213729555816239 21772188320594333724359)
          ·
            refine ⟨32658282480891500586539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21772188320594333724359 32658282480891500586539)
            ·
              refine ⟨48987423721337250879809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32658282480891500586539 48987423721337250879809)
              ·
                refine ⟨36740567791002938159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48987423721337250879809 36740567791002938159857)
                ·
                  refine ⟨27555425843252203619893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36740567791002938159857 27555425843252203619893)
                  ·
                    refine ⟨2583321172804894089365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27555425843252203619893 2583321172804894089365)
                    ·
                      rfl

theorem cell23_15093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_15093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15093 prefixEnd_15093 := by exact prefixLift 15093
  have htrace : WordTrace (prefixWord ++ tailWord_15093) baseStart_15093 baseEnd_15093 := by
    simpa [prefixWord, tailWord_15093, baseEnd_15093] using wordTrace_append hprefix tailTrace_15093
  have hstable : (prefixWord ++ tailWord_15093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15093).length < 2 ^ (prefixWord ++ tailWord_15093).sum := by decide
  have hdescent : baseEnd_15093 < baseStart_15093 := by decide
  rcases family_descends (prefixWord ++ tailWord_15093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15106 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_15106 : Nat := 118140960795 + 15106 * 2 ^ 59
def prefixEnd_15106 : Nat := 4983230072969 + 3 ^ 40 * 15106 * 2
def baseEnd_15106 : Nat := 2585546255641043801845

theorem tailTrace_15106 : CollatzResearch.WordTrace tailWord_15106 prefixEnd_15106 2585546255641043801845 := by
  unfold tailWord_15106
  simp only [CollatzResearch.WordTrace]
  refine ⟨137740270820254186128293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 367307388854011163008781 137740270820254186128293)
  ·
    refine ⟨25826300778797659899055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137740270820254186128293 25826300778797659899055)
    ·
      refine ⟨38739451168196489848583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25826300778797659899055 38739451168196489848583)
      ·
        refine ⟨58109176752294734772875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38739451168196489848583 58109176752294734772875)
        ·
          refine ⟨87163765128442102159313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58109176752294734772875 87163765128442102159313)
          ·
            refine ⟨65372823846331576619485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87163765128442102159313 65372823846331576619485)
            ·
              refine ⟨24514808942374341232307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65372823846331576619485 24514808942374341232307)
              ·
                refine ⟨36772213413561511848461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24514808942374341232307 36772213413561511848461)
                ·
                  refine ⟨13789580030085566943173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36772213413561511848461 13789580030085566943173)
                  ·
                    refine ⟨2585546255641043801845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13789580030085566943173 2585546255641043801845)
                    ·
                      rfl

theorem cell23_15106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_15106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15106 prefixEnd_15106 := by exact prefixLift 15106
  have htrace : WordTrace (prefixWord ++ tailWord_15106) baseStart_15106 baseEnd_15106 := by
    simpa [prefixWord, tailWord_15106, baseEnd_15106] using wordTrace_append hprefix tailTrace_15106
  have hstable : (prefixWord ++ tailWord_15106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15106).length < 2 ^ (prefixWord ++ tailWord_15106).sum := by decide
  have hdescent : baseEnd_15106 < baseStart_15106 := by decide
  rcases family_descends (prefixWord ++ tailWord_15106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15115 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 9]
def baseStart_15115 : Nat := 118140960795 + 15115 * 2 ^ 59
def prefixEnd_15115 : Nat := 4983230072969 + 3 ^ 40 * 15115 * 2
def baseEnd_15115 : Nat := 2587086697604532064331

theorem tailTrace_15115 : CollatzResearch.WordTrace tailWord_15115 prefixEnd_15115 2587086697604532064331 := by
  unfold tailWord_15115
  simp only [CollatzResearch.WordTrace]
  refine ⟨551289340248411281590799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 367526226832274187727199 551289340248411281590799)
  ·
    refine ⟨826934010372616922386199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551289340248411281590799 826934010372616922386199)
    ·
      refine ⟨1240401015558925383579299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 826934010372616922386199 1240401015558925383579299)
      ·
        refine ⟨1860601523338388075368949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240401015558925383579299 1860601523338388075368949)
        ·
          refine ⟨174431392812973882065839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1860601523338388075368949 174431392812973882065839)
          ·
            refine ⟨261647089219460823098759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174431392812973882065839 261647089219460823098759)
            ·
              refine ⟨392470633829191234648139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261647089219460823098759 392470633829191234648139)
              ·
                refine ⟨588705950743786851972209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 392470633829191234648139 588705950743786851972209)
                ·
                  refine ⟨441529463057840138979157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 588705950743786851972209 441529463057840138979157)
                  ·
                    refine ⟨2587086697604532064331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 441529463057840138979157 2587086697604532064331)
                    ·
                      rfl

theorem cell23_15115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_15115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15115 prefixEnd_15115 := by exact prefixLift 15115
  have htrace : WordTrace (prefixWord ++ tailWord_15115) baseStart_15115 baseEnd_15115 := by
    simpa [prefixWord, tailWord_15115, baseEnd_15115] using wordTrace_append hprefix tailTrace_15115
  have hstable : (prefixWord ++ tailWord_15115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15115).length < 2 ^ (prefixWord ++ tailWord_15115).sum := by decide
  have hdescent : baseEnd_15115 < baseStart_15115 := by decide
  rcases family_descends (prefixWord ++ tailWord_15115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15133 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 3]
def baseStart_15133 : Nat := 118140960795 + 15133 * 2 ^ 59
def prefixEnd_15133 : Nat := 4983230072969 + 3 ^ 40 * 15133 * 2
def baseEnd_15133 : Nat := 7770502744594525767911

theorem tailTrace_15133 : CollatzResearch.WordTrace tailWord_15133 prefixEnd_15133 7770502744594525767911 := by
  unfold tailWord_15133
  simp only [CollatzResearch.WordTrace]
  refine ⟨551945854183200355746053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 367963902788800237164035 551945854183200355746053)
  ·
    refine ⟨103489847659350066702385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 551945854183200355746053 103489847659350066702385)
    ·
      refine ⟨77617385744512550026789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103489847659350066702385 77617385744512550026789)
      ·
        refine ⟨14553259827096103130023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77617385744512550026789 14553259827096103130023)
        ·
          refine ⟨21829889740644154695035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553259827096103130023 21829889740644154695035)
          ·
            refine ⟨32744834610966232042553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21829889740644154695035 32744834610966232042553)
            ·
              refine ⟨24558625958224674031915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32744834610966232042553 24558625958224674031915)
              ·
                refine ⟨36837938937337011047873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24558625958224674031915 36837938937337011047873)
                ·
                  refine ⟨27628454203002758285905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36837938937337011047873 27628454203002758285905)
                  ·
                    refine ⟨20721340652252068714429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27628454203002758285905 20721340652252068714429)
                    ·
                      refine ⟨7770502744594525767911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20721340652252068714429 7770502744594525767911)
                      ·
                        rfl

theorem cell23_15133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_15133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15133 prefixEnd_15133 := by exact prefixLift 15133
  have htrace : WordTrace (prefixWord ++ tailWord_15133) baseStart_15133 baseEnd_15133 := by
    simpa [prefixWord, tailWord_15133, baseEnd_15133] using wordTrace_append hprefix tailTrace_15133
  have hstable : (prefixWord ++ tailWord_15133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15133).length < 2 ^ (prefixWord ++ tailWord_15133).sum := by decide
  have hdescent : baseEnd_15133 < baseStart_15133 := by decide
  rcases family_descends (prefixWord ++ tailWord_15133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15182 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_15182 : Nat := 118140960795 + 15182 * 2 ^ 59
def prefixEnd_15182 : Nat := 4983230072969 + 3 ^ 40 * 15182 * 2
def baseEnd_15182 : Nat := 7795663296664834055185

theorem tailTrace_15182 : CollatzResearch.WordTrace tailWord_15182 prefixEnd_15182 7795663296664834055185 := by
  unfold tailWord_15182
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216628875710215534975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 369155354003787816186533 69216628875710215534975)
  ·
    refine ⟨103824943313565323302463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69216628875710215534975 103824943313565323302463)
    ·
      refine ⟨155737414970347984953695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103824943313565323302463 155737414970347984953695)
      ·
        refine ⟨233606122455521977430543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155737414970347984953695 233606122455521977430543)
        ·
          refine ⟨350409183683282966145815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233606122455521977430543 350409183683282966145815)
          ·
            refine ⟨525613775524924449218723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350409183683282966145815 525613775524924449218723)
            ·
              refine ⟨788420663287386673828085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525613775524924449218723 788420663287386673828085)
              ·
                refine ⟨73914437183192500671383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 788420663287386673828085 73914437183192500671383)
                ·
                  refine ⟨110871655774788751007075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73914437183192500671383 110871655774788751007075)
                  ·
                    refine ⟨166307483662183126510613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 110871655774788751007075 166307483662183126510613)
                    ·
                      refine ⟨7795663296664834055185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 166307483662183126510613 7795663296664834055185)
                      ·
                        rfl

theorem cell23_15182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_15182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15182 prefixEnd_15182 := by exact prefixLift 15182
  have htrace : WordTrace (prefixWord ++ tailWord_15182) baseStart_15182 baseEnd_15182 := by
    simpa [prefixWord, tailWord_15182, baseEnd_15182] using wordTrace_append hprefix tailTrace_15182
  have hstable : (prefixWord ++ tailWord_15182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15182).length < 2 ^ (prefixWord ++ tailWord_15182).sum := by decide
  have hdescent : baseEnd_15182 < baseStart_15182 := by decide
  rcases family_descends (prefixWord ++ tailWord_15182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15189 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_15189 : Nat := 118140960795 + 15189 * 2 ^ 59
def prefixEnd_15189 : Nat := 4983230072969 + 3 ^ 40 * 15189 * 2
def baseEnd_15189 : Nat := 7799257661246306667653

theorem tailTrace_15189 : CollatzResearch.WordTrace tailWord_15189 prefixEnd_15189 7799257661246306667653 := by
  unfold tailWord_15189
  simp only [CollatzResearch.WordTrace]
  refine ⟨553988341980321919784621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 369325561320214613189747 553988341980321919784621)
  ·
    refine ⟨207745628242620719919233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 553988341980321919784621 207745628242620719919233)
    ·
      refine ⟨155809221181965539939425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207745628242620719919233 155809221181965539939425)
      ·
        refine ⟨116856915886474154954569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155809221181965539939425 116856915886474154954569)
        ·
          refine ⟨87642686914855616215927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116856915886474154954569 87642686914855616215927)
          ·
            refine ⟨131464030372283424323891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87642686914855616215927 131464030372283424323891)
            ·
              refine ⟨197196045558425136485837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131464030372283424323891 197196045558425136485837)
              ·
                refine ⟨73948517084409426182189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197196045558425136485837 73948517084409426182189)
                ·
                  refine ⟨27730693906653534818321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73948517084409426182189 27730693906653534818321)
                  ·
                    refine ⟨20798020429990151113741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27730693906653534818321 20798020429990151113741)
                    ·
                      refine ⟨7799257661246306667653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 20798020429990151113741 7799257661246306667653)
                      ·
                        rfl

theorem cell23_15189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_15189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15189 prefixEnd_15189 := by exact prefixLift 15189
  have htrace : WordTrace (prefixWord ++ tailWord_15189) baseStart_15189 baseEnd_15189 := by
    simpa [prefixWord, tailWord_15189, baseEnd_15189] using wordTrace_append hprefix tailTrace_15189
  have hstable : (prefixWord ++ tailWord_15189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15189).length < 2 ^ (prefixWord ++ tailWord_15189).sum := by decide
  have hdescent : baseEnd_15189 < baseStart_15189 := by decide
  rcases family_descends (prefixWord ++ tailWord_15189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15203 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 1, 1, 4]
def baseStart_15203 : Nat := 118140960795 + 15203 * 2 ^ 59
def prefixEnd_15203 : Nat := 4983230072969 + 3 ^ 40 * 15203 * 2
def baseEnd_15203 : Nat := 7806446390409251892589

theorem tailTrace_15203 : CollatzResearch.WordTrace tailWord_15203 prefixEnd_15203 7806446390409251892589 := by
  unfold tailWord_15203
  simp only [CollatzResearch.WordTrace]
  refine ⟨554498963929602310794263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 369665975953068207196175 554498963929602310794263)
  ·
    refine ⟨831748445894403466191395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 554498963929602310794263 831748445894403466191395)
    ·
      refine ⟨1247622668841605199287093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831748445894403466191395 1247622668841605199287093)
      ·
        refine ⟨116964625203900487433165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1247622668841605199287093 116964625203900487433165)
        ·
          refine ⟨43861734451462682787437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116964625203900487433165 43861734451462682787437)
          ·
            refine ⟨16448150419298506045289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43861734451462682787437 16448150419298506045289)
            ·
              refine ⟨12336112814473879533967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16448150419298506045289 12336112814473879533967)
              ·
                refine ⟨18504169221710819300951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336112814473879533967 18504169221710819300951)
                ·
                  refine ⟨27756253832566228951427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504169221710819300951 27756253832566228951427)
                  ·
                    refine ⟨41634380748849343427141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27756253832566228951427 41634380748849343427141)
                    ·
                      refine ⟨7806446390409251892589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 41634380748849343427141 7806446390409251892589)
                      ·
                        rfl

theorem cell23_15203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_15203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15203 prefixEnd_15203 := by exact prefixLift 15203
  have htrace : WordTrace (prefixWord ++ tailWord_15203) baseStart_15203 baseEnd_15203 := by
    simpa [prefixWord, tailWord_15203, baseEnd_15203] using wordTrace_append hprefix tailTrace_15203
  have hstable : (prefixWord ++ tailWord_15203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15203).length < 2 ^ (prefixWord ++ tailWord_15203).sum := by decide
  have hdescent : baseEnd_15203 < baseStart_15203 := by decide
  rcases family_descends (prefixWord ++ tailWord_15203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15230 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_15230 : Nat := 118140960795 + 15230 * 2 ^ 59
def prefixEnd_15230 : Nat := 4983230072969 + 3 ^ 40 * 15230 * 2
def baseEnd_15230 : Nat := 2606770122693548751655

theorem tailTrace_15230 : CollatzResearch.WordTrace tailWord_15230 prefixEnd_15230 2606770122693548751655 := by
  unfold tailWord_15230
  simp only [CollatzResearch.WordTrace]
  refine ⟨69435466853973240253393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 370322489887857281351429 69435466853973240253393)
  ·
    refine ⟨52076600140479930190045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69435466853973240253393 52076600140479930190045)
    ·
      refine ⟨19528725052679973821267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52076600140479930190045 19528725052679973821267)
      ·
        refine ⟨29293087579019960731901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19528725052679973821267 29293087579019960731901)
        ·
          refine ⟨10984907842132485274463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29293087579019960731901 10984907842132485274463)
          ·
            refine ⟨16477361763198727911695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10984907842132485274463 16477361763198727911695)
            ·
              refine ⟨24716042644798091867543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16477361763198727911695 24716042644798091867543)
              ·
                refine ⟨37074063967197137801315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24716042644798091867543 37074063967197137801315)
                ·
                  refine ⟨55611095950795706701973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37074063967197137801315 55611095950795706701973)
                  ·
                    refine ⟨2606770122693548751655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55611095950795706701973 2606770122693548751655)
                    ·
                      rfl

theorem cell23_15230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_15230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15230 prefixEnd_15230 := by exact prefixLift 15230
  have htrace : WordTrace (prefixWord ++ tailWord_15230) baseStart_15230 baseEnd_15230 := by
    simpa [prefixWord, tailWord_15230, baseEnd_15230] using wordTrace_append hprefix tailTrace_15230
  have hstable : (prefixWord ++ tailWord_15230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15230).length < 2 ^ (prefixWord ++ tailWord_15230).sum := by decide
  have hdescent : baseEnd_15230 < baseStart_15230 := by decide
  rcases family_descends (prefixWord ++ tailWord_15230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15263 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 1, 3, 2]
def baseStart_15263 : Nat := 118140960795 + 15263 * 2 ^ 59
def prefixEnd_15263 : Nat := 4983230072969 + 3 ^ 40 * 15263 * 2
def baseEnd_15263 : Nat := 7837255229679017142313

theorem tailTrace_15263 : CollatzResearch.WordTrace tailWord_15263 prefixEnd_15263 7837255229679017142313 := by
  unfold tailWord_15263
  simp only [CollatzResearch.WordTrace]
  refine ⟨556687343712232557978443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 371124895808155038652295 556687343712232557978443)
  ·
    refine ⟨835031015568348836967665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556687343712232557978443 835031015568348836967665)
    ·
      refine ⟨626273261676261627725749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 835031015568348836967665 626273261676261627725749)
      ·
        refine ⟨58713118282149527599289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 626273261676261627725749 58713118282149527599289)
        ·
          refine ⟨44034838711612145699467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58713118282149527599289 44034838711612145699467)
          ·
            refine ⟨66052258067418218549201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44034838711612145699467 66052258067418218549201)
            ·
              refine ⟨49539193550563663911901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66052258067418218549201 49539193550563663911901)
              ·
                refine ⟨18577197581461373966963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49539193550563663911901 18577197581461373966963)
                ·
                  refine ⟨27865796372192060950445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18577197581461373966963 27865796372192060950445)
                  ·
                    refine ⟨10449673639572022856417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27865796372192060950445 10449673639572022856417)
                    ·
                      refine ⟨7837255229679017142313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10449673639572022856417 7837255229679017142313)
                      ·
                        rfl

theorem cell23_15263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_15263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15263 prefixEnd_15263 := by exact prefixLift 15263
  have htrace : WordTrace (prefixWord ++ tailWord_15263) baseStart_15263 baseEnd_15263 := by
    simpa [prefixWord, tailWord_15263, baseEnd_15263] using wordTrace_append hprefix tailTrace_15263
  have hstable : (prefixWord ++ tailWord_15263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15263).length < 2 ^ (prefixWord ++ tailWord_15263).sum := by decide
  have hdescent : baseEnd_15263 < baseStart_15263 := by decide
  rcases family_descends (prefixWord ++ tailWord_15263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15336 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_15336 : Nat := 118140960795 + 15336 * 2 ^ 59
def prefixEnd_15336 : Nat := 4983230072969 + 3 ^ 40 * 15336 * 2
def baseEnd_15336 : Nat := 7874739317457231529477

theorem tailTrace_15336 : CollatzResearch.WordTrace tailWord_15336 prefixEnd_15336 7874739317457231529477 := by
  unfold tailWord_15336
  simp only [CollatzResearch.WordTrace]
  refine ⟨279674936223883012692931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 372899914965177350257241 279674936223883012692931)
  ·
    refine ⟨419512404335824519039397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279674936223883012692931 419512404335824519039397)
    ·
      refine ⟨78658575812967097319887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419512404335824519039397 78658575812967097319887)
      ·
        refine ⟨117987863719450645979831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78658575812967097319887 117987863719450645979831)
        ·
          refine ⟨176981795579175968969747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117987863719450645979831 176981795579175968969747)
          ·
            refine ⟨265472693368763953454621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176981795579175968969747 265472693368763953454621)
            ·
              refine ⟨99552260013286482545483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265472693368763953454621 99552260013286482545483)
              ·
                refine ⟨149328390019929723818225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99552260013286482545483 149328390019929723818225)
                ·
                  refine ⟨111996292514947292863669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149328390019929723818225 111996292514947292863669)
                  ·
                    refine ⟨10499652423276308705969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111996292514947292863669 10499652423276308705969)
                    ·
                      refine ⟨7874739317457231529477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10499652423276308705969 7874739317457231529477)
                      ·
                        rfl

theorem cell23_15336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_15336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15336 prefixEnd_15336 := by exact prefixLift 15336
  have htrace : WordTrace (prefixWord ++ tailWord_15336) baseStart_15336 baseEnd_15336 := by
    simpa [prefixWord, tailWord_15336, baseEnd_15336] using wordTrace_append hprefix tailTrace_15336
  have hstable : (prefixWord ++ tailWord_15336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15336).length < 2 ^ (prefixWord ++ tailWord_15336).sum := by decide
  have hdescent : baseEnd_15336 < baseStart_15336 := by decide
  rcases family_descends (prefixWord ++ tailWord_15336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15378 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_15378 : Nat := 118140960795 + 15378 * 2 ^ 59
def prefixEnd_15378 : Nat := 4983230072969 + 3 ^ 40 * 15378 * 2
def baseEnd_15378 : Nat := 7896305504946067204285

theorem tailTrace_15378 : CollatzResearch.WordTrace tailWord_15378 prefixEnd_15378 7896305504946067204285 := by
  unfold tailWord_15378
  simp only [CollatzResearch.WordTrace]
  refine ⟨140220434573901799603697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 373921158863738132276525 140220434573901799603697)
  ·
    refine ⟨105165325930426349702773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140220434573901799603697 105165325930426349702773)
    ·
      refine ⟨9859249305977470284635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105165325930426349702773 9859249305977470284635)
      ·
        refine ⟨14788873958966205426953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859249305977470284635 14788873958966205426953)
        ·
          refine ⟨11091655469224654070215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14788873958966205426953 11091655469224654070215)
          ·
            refine ⟨16637483203836981105323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11091655469224654070215 16637483203836981105323)
            ·
              refine ⟨24956224805755471657985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16637483203836981105323 24956224805755471657985)
              ·
                refine ⟨18717168604316603743489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24956224805755471657985 18717168604316603743489)
                ·
                  refine ⟨14037876453237452807617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18717168604316603743489 14037876453237452807617)
                  ·
                    refine ⟨10528407339928089605713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14037876453237452807617 10528407339928089605713)
                    ·
                      refine ⟨7896305504946067204285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10528407339928089605713 7896305504946067204285)
                      ·
                        rfl

theorem cell23_15378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_15378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15378 prefixEnd_15378 := by exact prefixLift 15378
  have htrace : WordTrace (prefixWord ++ tailWord_15378) baseStart_15378 baseEnd_15378 := by
    simpa [prefixWord, tailWord_15378, baseEnd_15378] using wordTrace_append hprefix tailTrace_15378
  have hstable : (prefixWord ++ tailWord_15378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15378).length < 2 ^ (prefixWord ++ tailWord_15378).sum := by decide
  have hdescent : baseEnd_15378 < baseStart_15378 := by decide
  rcases family_descends (prefixWord ++ tailWord_15378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15383 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_15383 : Nat := 118140960795 + 15383 * 2 ^ 59
def prefixEnd_15383 : Nat := 4983230072969 + 3 ^ 40 * 15383 * 2
def baseEnd_15383 : Nat := 7898872908218547641761

theorem tailTrace_15383 : CollatzResearch.WordTrace tailWord_15383 prefixEnd_15383 7898872908218547641761 := by
  unfold tailWord_15383
  simp only [CollatzResearch.WordTrace]
  refine ⟨561064103277493052346803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 374042735518328701564535 561064103277493052346803)
  ·
    refine ⟨841596154916239578520205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561064103277493052346803 841596154916239578520205)
    ·
      refine ⟨315598558093589841945077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 841596154916239578520205 315598558093589841945077)
      ·
        refine ⟨29587364821274047682351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315598558093589841945077 29587364821274047682351)
        ·
          refine ⟨44381047231911071523527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29587364821274047682351 44381047231911071523527)
          ·
            refine ⟨66571570847866607285291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44381047231911071523527 66571570847866607285291)
            ·
              refine ⟨99857356271799910927937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66571570847866607285291 99857356271799910927937)
              ·
                refine ⟨74893017203849933195953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99857356271799910927937 74893017203849933195953)
                ·
                  refine ⟨56169762902887449896965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74893017203849933195953 56169762902887449896965)
                  ·
                    refine ⟨10531830544291396855681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56169762902887449896965 10531830544291396855681)
                    ·
                      refine ⟨7898872908218547641761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10531830544291396855681 7898872908218547641761)
                      ·
                        rfl

theorem cell23_15383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_15383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15383 prefixEnd_15383 := by exact prefixLift 15383
  have htrace : WordTrace (prefixWord ++ tailWord_15383) baseStart_15383 baseEnd_15383 := by
    simpa [prefixWord, tailWord_15383, baseEnd_15383] using wordTrace_append hprefix tailTrace_15383
  have hstable : (prefixWord ++ tailWord_15383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15383).length < 2 ^ (prefixWord ++ tailWord_15383).sum := by decide
  have hdescent : baseEnd_15383 < baseStart_15383 := by decide
  rcases family_descends (prefixWord ++ tailWord_15383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15386 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_15386 : Nat := 118140960795 + 15386 * 2 ^ 59
def prefixEnd_15386 : Nat := 4983230072969 + 3 ^ 40 * 15386 * 2
def baseEnd_15386 : Nat := 7900413350182035904247

theorem tailTrace_15386 : CollatzResearch.WordTrace tailWord_15386 prefixEnd_15386 7900413350182035904247 := by
  unfold tailWord_15386
  simp only [CollatzResearch.WordTrace]
  refine ⟨140293380566656141176503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 374115681511083043137341 140293380566656141176503)
  ·
    refine ⟨210440070849984211764755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140293380566656141176503 210440070849984211764755)
    ·
      refine ⟨315660106274976317647133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210440070849984211764755 315660106274976317647133)
      ·
        refine ⟨118372539853116119117675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315660106274976317647133 118372539853116119117675)
        ·
          refine ⟨177558809779674178676513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118372539853116119117675 177558809779674178676513)
          ·
            refine ⟨133169107334755634007385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177558809779674178676513 133169107334755634007385)
            ·
              refine ⟨99876830501066725505539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133169107334755634007385 99876830501066725505539)
              ·
                refine ⟨149815245751600088258309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99876830501066725505539 149815245751600088258309)
                ·
                  refine ⟨28090358578425016548433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149815245751600088258309 28090358578425016548433)
                  ·
                    refine ⟨21067768933818762411325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28090358578425016548433 21067768933818762411325)
                    ·
                      refine ⟨7900413350182035904247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21067768933818762411325 7900413350182035904247)
                      ·
                        rfl

theorem cell23_15386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_15386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15386 prefixEnd_15386 := by exact prefixLift 15386
  have htrace : WordTrace (prefixWord ++ tailWord_15386) baseStart_15386 baseEnd_15386 := by
    simpa [prefixWord, tailWord_15386, baseEnd_15386] using wordTrace_append hprefix tailTrace_15386
  have hstable : (prefixWord ++ tailWord_15386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15386).length < 2 ^ (prefixWord ++ tailWord_15386).sum := by decide
  have hdescent : baseEnd_15386 < baseStart_15386 := by decide
  rcases family_descends (prefixWord ++ tailWord_15386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15393 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 3, 4]
def baseStart_15393 : Nat := 118140960795 + 15393 * 2 ^ 59
def prefixEnd_15393 : Nat := 4983230072969 + 3 ^ 40 * 15393 * 2
def baseEnd_15393 : Nat := 2634669238254502838905

theorem tailTrace_15393 : CollatzResearch.WordTrace tailWord_15393 prefixEnd_15393 2634669238254502838905 := by
  unfold tailWord_15393
  simp only [CollatzResearch.WordTrace]
  refine ⟨561428833241264760210833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 374285888827509840140555 561428833241264760210833)
  ·
    refine ⟨421071624930948570158125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 561428833241264760210833 421071624930948570158125)
    ·
      refine ⟨157901859349105713809297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421071624930948570158125 157901859349105713809297)
      ·
        refine ⟨118426394511829285356973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157901859349105713809297 118426394511829285356973)
        ·
          refine ⟨44409897941935982008865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118426394511829285356973 44409897941935982008865)
          ·
            refine ⟨33307423456451986506649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44409897941935982008865 33307423456451986506649)
            ·
              refine ⟨24980567592338989879987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33307423456451986506649 24980567592338989879987)
              ·
                refine ⟨37470851388508484819981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24980567592338989879987 37470851388508484819981)
                ·
                  refine ⟨14051569270690681807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37470851388508484819981 14051569270690681807493)
                  ·
                    refine ⟨2634669238254502838905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14051569270690681807493 2634669238254502838905)
                    ·
                      rfl

theorem cell23_15393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_15393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15393 prefixEnd_15393 := by exact prefixLift 15393
  have htrace : WordTrace (prefixWord ++ tailWord_15393) baseStart_15393 baseEnd_15393 := by
    simpa [prefixWord, tailWord_15393, baseEnd_15393] using wordTrace_append hprefix tailTrace_15393
  have hstable : (prefixWord ++ tailWord_15393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15393).length < 2 ^ (prefixWord ++ tailWord_15393).sum := by decide
  have hdescent : baseEnd_15393 < baseStart_15393 := by decide
  rcases family_descends (prefixWord ++ tailWord_15393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15409 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_15409 : Nat := 118140960795 + 15409 * 2 ^ 59
def prefixEnd_15409 : Nat := 4983230072969 + 3 ^ 40 * 15409 * 2
def baseEnd_15409 : Nat := 7912223405235445916641

theorem tailTrace_15409 : CollatzResearch.WordTrace tailWord_15409 prefixEnd_15409 7912223405235445916641 := by
  unfold tailWord_15409
  simp only [CollatzResearch.WordTrace]
  refine ⟨562012401183299492793281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 374674934122199661862187 562012401183299492793281)
  ·
    refine ⟨421509300887474619594961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562012401183299492793281 421509300887474619594961)
    ·
      refine ⟨316131975665605964696221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421509300887474619594961 316131975665605964696221)
      ·
        refine ⟨118549490874602236761083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 316131975665605964696221 118549490874602236761083)
        ·
          refine ⟨177824236311903355141625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118549490874602236761083 177824236311903355141625)
          ·
            refine ⟨133368177233927516356219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177824236311903355141625 133368177233927516356219)
            ·
              refine ⟨200052265850891274534329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133368177233927516356219 200052265850891274534329)
              ·
                refine ⟨150039199388168455900747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200052265850891274534329 150039199388168455900747)
                ·
                  refine ⟨225058799082252683851121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150039199388168455900747 225058799082252683851121)
                  ·
                    refine ⟨168794099311689512888341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 225058799082252683851121 168794099311689512888341)
                    ·
                      refine ⟨7912223405235445916641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 168794099311689512888341 7912223405235445916641)
                      ·
                        rfl

theorem cell23_15409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_15409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15409 prefixEnd_15409 := by exact prefixLift 15409
  have htrace : WordTrace (prefixWord ++ tailWord_15409) baseStart_15409 baseEnd_15409 := by
    simpa [prefixWord, tailWord_15409, baseEnd_15409] using wordTrace_append hprefix tailTrace_15409
  have hstable : (prefixWord ++ tailWord_15409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15409).length < 2 ^ (prefixWord ++ tailWord_15409).sum := by decide
  have hdescent : baseEnd_15409 < baseStart_15409 := by decide
  rcases family_descends (prefixWord ++ tailWord_15409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15449 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 6]
def baseStart_15449 : Nat := 118140960795 + 15449 * 2 ^ 59
def prefixEnd_15449 : Nat := 4983230072969 + 3 ^ 40 * 15449 * 2
def baseEnd_15449 : Nat := 2644254210471763138819

theorem tailTrace_15449 : CollatzResearch.WordTrace tailWord_15449 prefixEnd_15449 2644254210471763138819 := by
  unfold tailWord_15449
  simp only [CollatzResearch.WordTrace]
  refine ⟨563471321038386324249401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 375647547358924216166267 563471321038386324249401)
  ·
    refine ⟨422603490778789743187051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 563471321038386324249401 422603490778789743187051)
    ·
      refine ⟨633905236168184614780577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422603490778789743187051 633905236168184614780577)
      ·
        refine ⟨475428927126138461085433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633905236168184614780577 475428927126138461085433)
        ·
          refine ⟨356571695344603845814075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475428927126138461085433 356571695344603845814075)
          ·
            refine ⟨534857543016905768721113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356571695344603845814075 534857543016905768721113)
            ·
              refine ⟨401143157262679326540835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534857543016905768721113 401143157262679326540835)
              ·
                refine ⟨601714735894018989811253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401143157262679326540835 601714735894018989811253)
                ·
                  refine ⟨56410756490064280294805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 601714735894018989811253 56410756490064280294805)
                  ·
                    refine ⟨2644254210471763138819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56410756490064280294805 2644254210471763138819)
                    ·
                      rfl

theorem cell23_15449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_15449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15449 prefixEnd_15449 := by exact prefixLift 15449
  have htrace : WordTrace (prefixWord ++ tailWord_15449) baseStart_15449 baseEnd_15449 := by
    simpa [prefixWord, tailWord_15449, baseEnd_15449] using wordTrace_append hprefix tailTrace_15449
  have hstable : (prefixWord ++ tailWord_15449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15449).length < 2 ^ (prefixWord ++ tailWord_15449).sum := by decide
  have hdescent : baseEnd_15449 < baseStart_15449 := by decide
  rcases family_descends (prefixWord ++ tailWord_15449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15456 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_15456 : Nat := 118140960795 + 15456 * 2 ^ 59
def prefixEnd_15456 : Nat := 4983230072969 + 3 ^ 40 * 15456 * 2
def baseEnd_15456 : Nat := 7936356995996762028925

theorem tailTrace_15456 : CollatzResearch.WordTrace tailWord_15456 prefixEnd_15456 7936356995996762028925 := by
  unfold tailWord_15456
  simp only [CollatzResearch.WordTrace]
  refine ⟨281863316006513259877111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 375817754675351013169481 281863316006513259877111)
  ·
    refine ⟨422794974009769889815667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 281863316006513259877111 422794974009769889815667)
    ·
      refine ⟨634192461014654834723501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422794974009769889815667 634192461014654834723501)
      ·
        refine ⟨237822172880495563021313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634192461014654834723501 237822172880495563021313)
        ·
          refine ⟨178366629660371672265985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237822172880495563021313 178366629660371672265985)
          ·
            refine ⟨133774972245278754199489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178366629660371672265985 133774972245278754199489)
            ·
              refine ⟨100331229183959065649617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133774972245278754199489 100331229183959065649617)
              ·
                refine ⟨75248421887969299237213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100331229183959065649617 75248421887969299237213)
                ·
                  refine ⟨28218158207988487213955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75248421887969299237213 28218158207988487213955)
                  ·
                    refine ⟨42327237311982730820933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28218158207988487213955 42327237311982730820933)
                    ·
                      refine ⟨7936356995996762028925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 42327237311982730820933 7936356995996762028925)
                      ·
                        rfl

theorem cell23_15456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_15456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15456 prefixEnd_15456 := by exact prefixLift 15456
  have htrace : WordTrace (prefixWord ++ tailWord_15456) baseStart_15456 baseEnd_15456 := by
    simpa [prefixWord, tailWord_15456, baseEnd_15456] using wordTrace_append hprefix tailTrace_15456
  have hstable : (prefixWord ++ tailWord_15456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15456).length < 2 ^ (prefixWord ++ tailWord_15456).sum := by decide
  have hdescent : baseEnd_15456 < baseStart_15456 := by decide
  rcases family_descends (prefixWord ++ tailWord_15456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15470 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_15470 : Nat := 118140960795 + 15470 * 2 ^ 59
def prefixEnd_15470 : Nat := 4983230072969 + 3 ^ 40 * 15470 * 2
def baseEnd_15470 : Nat := 2647848575053235751287

theorem tailTrace_15470 : CollatzResearch.WordTrace tailWord_15470 prefixEnd_15470 2647848575053235751287 := by
  unfold tailWord_15470
  simp only [CollatzResearch.WordTrace]
  refine ⟨70529656745288363845483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 376158169308204607175909 70529656745288363845483)
  ·
    refine ⟨105794485117932545768225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70529656745288363845483 105794485117932545768225)
    ·
      refine ⟨79345863838449409326169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105794485117932545768225 79345863838449409326169)
      ·
        refine ⟨59509397878837056994627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79345863838449409326169 59509397878837056994627)
        ·
          refine ⟨89264096818255585491941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59509397878837056994627 89264096818255585491941)
          ·
            refine ⟨16737018153422922279739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89264096818255585491941 16737018153422922279739)
            ·
              refine ⟨25105527230134383419609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16737018153422922279739 25105527230134383419609)
              ·
                refine ⟨18829145422600787564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25105527230134383419609 18829145422600787564707)
                ·
                  refine ⟨28243718133901181347061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18829145422600787564707 28243718133901181347061)
                  ·
                    refine ⟨2647848575053235751287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28243718133901181347061 2647848575053235751287)
                    ·
                      rfl

theorem cell23_15470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_15470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15470 prefixEnd_15470 := by exact prefixLift 15470
  have htrace : WordTrace (prefixWord ++ tailWord_15470) baseStart_15470 baseEnd_15470 := by
    simpa [prefixWord, tailWord_15470, baseEnd_15470] using wordTrace_append hprefix tailTrace_15470
  have hstable : (prefixWord ++ tailWord_15470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15470).length < 2 ^ (prefixWord ++ tailWord_15470).sum := by decide
  have hdescent : baseEnd_15470 < baseStart_15470 := by decide
  rcases family_descends (prefixWord ++ tailWord_15470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15479 : List Nat := [1, 1, 3, 1, 1, 4, 1, 11]
def baseStart_15479 : Nat := 118140960795 + 15479 * 2 ^ 59
def prefixEnd_15479 : Nat := 4983230072969 + 3 ^ 40 * 15479 * 2
def baseEnd_15479 : Nat := 294376557446302668197

theorem tailTrace_15479 : CollatzResearch.WordTrace tailWord_15479 prefixEnd_15479 294376557446302668197 := by
  unfold tailWord_15479
  simp only [CollatzResearch.WordTrace]
  refine ⟨564565510929701447841491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 376377007286467631894327 564565510929701447841491)
  ·
    refine ⟨846848266394552171762237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564565510929701447841491 846848266394552171762237)
    ·
      refine ⟨317568099897957064410839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 846848266394552171762237 317568099897957064410839)
      ·
        refine ⟨476352149846935596616259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317568099897957064410839 476352149846935596616259)
        ·
          refine ⟨714528224770403394924389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476352149846935596616259 714528224770403394924389)
          ·
            refine ⟨133974042144450636548323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 714528224770403394924389 133974042144450636548323)
            ·
              refine ⟨200961063216675954822485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133974042144450636548323 200961063216675954822485)
              ·
                refine ⟨294376557446302668197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 200961063216675954822485 294376557446302668197)
                ·
                  rfl

theorem cell23_15479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 11].length) (baseStart_15479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15479 prefixEnd_15479 := by exact prefixLift 15479
  have htrace : WordTrace (prefixWord ++ tailWord_15479) baseStart_15479 baseEnd_15479 := by
    simpa [prefixWord, tailWord_15479, baseEnd_15479] using wordTrace_append hprefix tailTrace_15479
  have hstable : (prefixWord ++ tailWord_15479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15479).length < 2 ^ (prefixWord ++ tailWord_15479).sum := by decide
  have hdescent : baseEnd_15479 < baseStart_15479 := by decide
  rcases family_descends (prefixWord ++ tailWord_15479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15496 : List Nat := [2, 1, 3, 4, 2, 11]
def baseStart_15496 : Nat := 118140960795 + 15496 * 2 ^ 59
def prefixEnd_15496 : Nat := 4983230072969 + 3 ^ 40 * 15496 * 2
def baseEnd_15496 : Nat := 32744428897846113287

theorem tailTrace_15496 : CollatzResearch.WordTrace tailWord_15496 prefixEnd_15496 32744428897846113287 := by
  unfold tailWord_15496
  simp only [CollatzResearch.WordTrace]
  refine ⟨282592775934056675605171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 376790367912075567473561 282592775934056675605171)
  ·
    refine ⟨423889163901085013407757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282592775934056675605171 423889163901085013407757)
    ·
      refine ⟨158958436462906880027909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423889163901085013407757 158958436462906880027909)
      ·
        refine ⟨29804706836795040005233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158958436462906880027909 29804706836795040005233)
        ·
          refine ⟨22353530127596280003925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29804706836795040005233 22353530127596280003925)
          ·
            refine ⟨32744428897846113287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 22353530127596280003925 32744428897846113287)
            ·
              rfl

theorem cell23_15496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 11].length) (baseStart_15496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15496 prefixEnd_15496 := by exact prefixLift 15496
  have htrace : WordTrace (prefixWord ++ tailWord_15496) baseStart_15496 baseEnd_15496 := by
    simpa [prefixWord, tailWord_15496, baseEnd_15496] using wordTrace_append hprefix tailTrace_15496
  have hstable : (prefixWord ++ tailWord_15496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15496).length < 2 ^ (prefixWord ++ tailWord_15496).sum := by decide
  have hdescent : baseEnd_15496 < baseStart_15496 := by decide
  rcases family_descends (prefixWord ++ tailWord_15496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15530 : List Nat := [3, 1, 5, 1, 1, 2, 3, 7]
def baseStart_15530 : Nat := 118140960795 + 15530 * 2 ^ 59
def prefixEnd_15530 : Nat := 4983230072969 + 3 ^ 40 * 15530 * 2
def baseEnd_15530 : Nat := 295346465349239722355

theorem tailTrace_15530 : CollatzResearch.WordTrace tailWord_15530 prefixEnd_15530 295346465349239722355 := by
  unfold tailWord_15530
  simp only [CollatzResearch.WordTrace]
  refine ⟨141606408436234289487011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 377617089163291438632029 141606408436234289487011)
  ·
    refine ⟨212409612654351434230517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141606408436234289487011 212409612654351434230517)
    ·
      refine ⟨19913401186345446959111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212409612654351434230517 19913401186345446959111)
      ·
        refine ⟨29870101779518170438667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19913401186345446959111 29870101779518170438667)
        ·
          refine ⟨44805152669277255658001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29870101779518170438667 44805152669277255658001)
          ·
            refine ⟨33603864501957941743501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44805152669277255658001 33603864501957941743501)
            ·
              refine ⟨12601449188234228153813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33603864501957941743501 12601449188234228153813)
              ·
                refine ⟨295346465349239722355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12601449188234228153813 295346465349239722355)
                ·
                  rfl

theorem cell23_15530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_15530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15530 prefixEnd_15530 := by exact prefixLift 15530
  have htrace : WordTrace (prefixWord ++ tailWord_15530) baseStart_15530 baseEnd_15530 := by
    simpa [prefixWord, tailWord_15530, baseEnd_15530] using wordTrace_append hprefix tailTrace_15530
  have hstable : (prefixWord ++ tailWord_15530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15530).length < 2 ^ (prefixWord ++ tailWord_15530).sum := by decide
  have hdescent : baseEnd_15530 < baseStart_15530 := by decide
  rcases family_descends (prefixWord ++ tailWord_15530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15558 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_15558 : Nat := 118140960795 + 15558 * 2 ^ 59
def prefixEnd_15558 : Nat := 4983230072969 + 3 ^ 40 * 15558 * 2
def baseEnd_15558 : Nat := 7988732022755362953457

theorem tailTrace_15558 : CollatzResearch.WordTrace tailWord_15558 prefixEnd_15558 7988732022755362953457 := by
  unfold tailWord_15558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17732714926359310623979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 378297918428998626644885 17732714926359310623979)
  ·
    refine ⟨26599072389538965935969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17732714926359310623979 26599072389538965935969)
    ·
      refine ⟨19949304292154224451977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26599072389538965935969 19949304292154224451977)
      ·
        refine ⟨14961978219115668338983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19949304292154224451977 14961978219115668338983)
        ·
          refine ⟨22442967328673502508475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14961978219115668338983 22442967328673502508475)
          ·
            refine ⟨33664450993010253762713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22442967328673502508475 33664450993010253762713)
            ·
              refine ⟨25248338244757690322035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33664450993010253762713 25248338244757690322035)
              ·
                refine ⟨37872507367136535483053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25248338244757690322035 37872507367136535483053)
                ·
                  refine ⟨14202190262676200806145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37872507367136535483053 14202190262676200806145)
                  ·
                    refine ⟨10651642697007150604609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14202190262676200806145 10651642697007150604609)
                    ·
                      refine ⟨7988732022755362953457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10651642697007150604609 7988732022755362953457)
                      ·
                        rfl

theorem cell23_15558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_15558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15558 prefixEnd_15558 := by exact prefixLift 15558
  have htrace : WordTrace (prefixWord ++ tailWord_15558) baseStart_15558 baseEnd_15558 := by
    simpa [prefixWord, tailWord_15558, baseEnd_15558] using wordTrace_append hprefix tailTrace_15558
  have hstable : (prefixWord ++ tailWord_15558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15558).length < 2 ^ (prefixWord ++ tailWord_15558).sum := by decide
  have hdescent : baseEnd_15558 < baseStart_15558 := by decide
  rcases family_descends (prefixWord ++ tailWord_15558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15573 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_15573 : Nat := 118140960795 + 15573 * 2 ^ 59
def prefixEnd_15573 : Nat := 4983230072969 + 3 ^ 40 * 15573 * 2
def baseEnd_15573 : Nat := 2665478077524268088629

theorem tailTrace_15573 : CollatzResearch.WordTrace tailWord_15573 prefixEnd_15573 2665478077524268088629 := by
  unfold tailWord_15573
  simp only [CollatzResearch.WordTrace]
  refine ⟨567993972589155501763373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 378662648392770334508915 567993972589155501763373)
  ·
    refine ⟨212997739720933313161265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 567993972589155501763373 212997739720933313161265)
    ·
      refine ⟨159748304790699984870949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212997739720933313161265 159748304790699984870949)
      ·
        refine ⟨29952807148256247163303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159748304790699984870949 29952807148256247163303)
        ·
          refine ⟨44929210722384370744955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29952807148256247163303 44929210722384370744955)
          ·
            refine ⟨67393816083576556117433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44929210722384370744955 67393816083576556117433)
            ·
              refine ⟨50545362062682417088075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67393816083576556117433 50545362062682417088075)
              ·
                refine ⟨75818043094023625632113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50545362062682417088075 75818043094023625632113)
                ·
                  refine ⟨56863532320517719224085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75818043094023625632113 56863532320517719224085)
                  ·
                    refine ⟨2665478077524268088629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56863532320517719224085 2665478077524268088629)
                    ·
                      rfl

theorem cell23_15573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_15573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15573 prefixEnd_15573 := by exact prefixLift 15573
  have htrace : WordTrace (prefixWord ++ tailWord_15573) baseStart_15573 baseEnd_15573 := by
    simpa [prefixWord, tailWord_15573, baseEnd_15573] using wordTrace_append hprefix tailTrace_15573
  have hstable : (prefixWord ++ tailWord_15573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15573).length < 2 ^ (prefixWord ++ tailWord_15573).sum := by decide
  have hdescent : baseEnd_15573 < baseStart_15573 := by decide
  rcases family_descends (prefixWord ++ tailWord_15573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15574 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_15574 : Nat := 118140960795 + 15574 * 2 ^ 59
def prefixEnd_15574 : Nat := 4983230072969 + 3 ^ 40 * 15574 * 2
def baseEnd_15574 : Nat := 7996947713227300353383

theorem tailTrace_15574 : CollatzResearch.WordTrace tailWord_15574 prefixEnd_15574 7996947713227300353383 := by
  unfold tailWord_15574
  simp only [CollatzResearch.WordTrace]
  refine ⟨35501902849095792034361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 378686963723688448366517 35501902849095792034361)
  ·
    refine ⟨26626427136821844025771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35501902849095792034361 26626427136821844025771)
    ·
      refine ⟨39939640705232766038657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26626427136821844025771 39939640705232766038657)
      ·
        refine ⟨29954730528924574528993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39939640705232766038657 29954730528924574528993)
        ·
          refine ⟨22466047896693430896745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29954730528924574528993 22466047896693430896745)
          ·
            refine ⟨16849535922520073172559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22466047896693430896745 16849535922520073172559)
            ·
              refine ⟨25274303883780109758839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16849535922520073172559 25274303883780109758839)
              ·
                refine ⟨37911455825670164638259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25274303883780109758839 37911455825670164638259)
                ·
                  refine ⟨56867183738505246957389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37911455825670164638259 56867183738505246957389)
                  ·
                    refine ⟨21325193901939467609021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56867183738505246957389 21325193901939467609021)
                    ·
                      refine ⟨7996947713227300353383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21325193901939467609021 7996947713227300353383)
                      ·
                        rfl

theorem cell23_15574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_15574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15574 prefixEnd_15574 := by exact prefixLift 15574
  have htrace : WordTrace (prefixWord ++ tailWord_15574) baseStart_15574 baseEnd_15574 := by
    simpa [prefixWord, tailWord_15574, baseEnd_15574] using wordTrace_append hprefix tailTrace_15574
  have hstable : (prefixWord ++ tailWord_15574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15574).length < 2 ^ (prefixWord ++ tailWord_15574).sum := by decide
  have hdescent : baseEnd_15574 < baseStart_15574 := by decide
  rcases family_descends (prefixWord ++ tailWord_15574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15597 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_15597 : Nat := 118140960795 + 15597 * 2 ^ 59
def prefixEnd_15597 : Nat := 4983230072969 + 3 ^ 40 * 15597 * 2
def baseEnd_15597 : Nat := 8008757768280710365777

theorem tailTrace_15597 : CollatzResearch.WordTrace tailWord_15597 prefixEnd_15597 8008757768280710365777 := by
  unfold tailWord_15597
  simp only [CollatzResearch.WordTrace]
  refine ⟨568869324502207600637045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 379246216334805067091363 568869324502207600637045)
  ·
    refine ⟨53331499172081962559723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 568869324502207600637045 53331499172081962559723)
    ·
      refine ⟨79997248758122943839585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53331499172081962559723 79997248758122943839585)
      ·
        refine ⟨59997936568592207879689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79997248758122943839585 59997936568592207879689)
        ·
          refine ⟨44998452426444155909767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59997936568592207879689 44998452426444155909767)
          ·
            refine ⟨67497678639666233864651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44998452426444155909767 67497678639666233864651)
            ·
              refine ⟨101246517959499350796977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67497678639666233864651 101246517959499350796977)
              ·
                refine ⟨75934888469624513097733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101246517959499350796977 75934888469624513097733)
                ·
                  refine ⟨14237791588054596205825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75934888469624513097733 14237791588054596205825)
                  ·
                    refine ⟨10678343691040947154369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14237791588054596205825 10678343691040947154369)
                    ·
                      refine ⟨8008757768280710365777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10678343691040947154369 8008757768280710365777)
                      ·
                        rfl

theorem cell23_15597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_15597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15597 prefixEnd_15597 := by exact prefixLift 15597
  have htrace : WordTrace (prefixWord ++ tailWord_15597) baseStart_15597 baseEnd_15597 := by
    simpa [prefixWord, tailWord_15597, baseEnd_15597] using wordTrace_append hprefix tailTrace_15597
  have hstable : (prefixWord ++ tailWord_15597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15597).length < 2 ^ (prefixWord ++ tailWord_15597).sum := by decide
  have hdescent : baseEnd_15597 < baseStart_15597 := by decide
  rcases family_descends (prefixWord ++ tailWord_15597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15620 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 7]
def baseStart_15620 : Nat := 118140960795 + 15620 * 2 ^ 59
def prefixEnd_15620 : Nat := 4983230072969 + 3 ^ 40 * 15620 * 2
def baseEnd_15620 : Nat := 891174202592680042019

theorem tailTrace_15620 : CollatzResearch.WordTrace tailWord_15620 prefixEnd_15620 891174202592680042019 := by
  unfold tailWord_15620
  simp only [CollatzResearch.WordTrace]
  refine ⟨284854101709441264362157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 379805468945921685816209 284854101709441264362157)
  ·
    refine ⟨106820288141040474135809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284854101709441264362157 106820288141040474135809)
    ·
      refine ⟨80115216105780355601857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106820288141040474135809 80115216105780355601857)
      ·
        refine ⟨60086412079335266701393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80115216105780355601857 60086412079335266701393)
        ·
          refine ⟨45064809059501450026045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60086412079335266701393 45064809059501450026045)
          ·
            refine ⟨16899303397313043759767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45064809059501450026045 16899303397313043759767)
            ·
              refine ⟨25348955095969565639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16899303397313043759767 25348955095969565639651)
              ·
                refine ⟨38023432643954348459477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25348955095969565639651 38023432643954348459477)
                ·
                  refine ⟨891174202592680042019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38023432643954348459477 891174202592680042019)
                  ·
                    rfl

theorem cell23_15620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_15620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15620 prefixEnd_15620 := by exact prefixLift 15620
  have htrace : WordTrace (prefixWord ++ tailWord_15620) baseStart_15620 baseEnd_15620 := by
    simpa [prefixWord, tailWord_15620, baseEnd_15620] using wordTrace_append hprefix tailTrace_15620
  have hstable : (prefixWord ++ tailWord_15620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15620).length < 2 ^ (prefixWord ++ tailWord_15620).sum := by decide
  have hdescent : baseEnd_15620 < baseStart_15620 := by decide
  rcases family_descends (prefixWord ++ tailWord_15620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15714 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_15714 : Nat := 118140960795 + 15714 * 2 ^ 59
def prefixEnd_15714 : Nat := 4983230072969 + 3 ^ 40 * 15714 * 2
def baseEnd_15714 : Nat := 2689611668285584200913

theorem tailTrace_15714 : CollatzResearch.WordTrace tailWord_15714 prefixEnd_15714 2689611668285584200913 := by
  unfold tailWord_15714
  simp only [CollatzResearch.WordTrace]
  refine ⟨143284166269584145661549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 382091110052224388430797 143284166269584145661549)
  ·
    refine ⟨53731562351094054623081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143284166269584145661549 53731562351094054623081)
    ·
      refine ⟨40298671763320540967311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53731562351094054623081 40298671763320540967311)
      ·
        refine ⟨60448007644980811450967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40298671763320540967311 60448007644980811450967)
        ·
          refine ⟨90672011467471217176451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60448007644980811450967 90672011467471217176451)
          ·
            refine ⟨136008017201206825764677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90672011467471217176451 136008017201206825764677)
            ·
              refine ⟨25501503225226279830877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136008017201206825764677 25501503225226279830877)
              ·
                refine ⟨9563063709459854936579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25501503225226279830877 9563063709459854936579)
                ·
                  refine ⟨14344595564189782404869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9563063709459854936579 14344595564189782404869)
                  ·
                    refine ⟨2689611668285584200913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14344595564189782404869 2689611668285584200913)
                    ·
                      rfl

theorem cell23_15714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_15714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15714 prefixEnd_15714 := by exact prefixLift 15714
  have htrace : WordTrace (prefixWord ++ tailWord_15714) baseStart_15714 baseEnd_15714 := by
    simpa [prefixWord, tailWord_15714, baseEnd_15714] using wordTrace_append hprefix tailTrace_15714
  have hstable : (prefixWord ++ tailWord_15714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15714).length < 2 ^ (prefixWord ++ tailWord_15714).sum := by decide
  have hdescent : baseEnd_15714 < baseStart_15714 := by decide
  rcases family_descends (prefixWord ++ tailWord_15714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15763 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3]
def baseStart_15763 : Nat := 118140960795 + 15763 * 2 ^ 59
def prefixEnd_15763 : Nat := 4983230072969 + 3 ^ 40 * 15763 * 2
def baseEnd_15763 : Nat := 8093995556927060890013

theorem tailTrace_15763 : CollatzResearch.WordTrace tailWord_15763 prefixEnd_15763 8093995556927060890013 := by
  unfold tailWord_15763
  simp only [CollatzResearch.WordTrace]
  refine ⟨574923841900817951179943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 383282561267211967453295 574923841900817951179943)
  ·
    refine ⟨862385762851226926769915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574923841900817951179943 862385762851226926769915)
    ·
      refine ⟨1293578644276840390154873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862385762851226926769915 1293578644276840390154873)
      ·
        refine ⟨970183983207630292616155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293578644276840390154873 970183983207630292616155)
        ·
          refine ⟨1455275974811445438924233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970183983207630292616155 1455275974811445438924233)
          ·
            refine ⟨1091456981108584079193175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455275974811445438924233 1091456981108584079193175)
            ·
              refine ⟨1637185471662876118789763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091456981108584079193175 1637185471662876118789763)
              ·
                refine ⟨2455778207494314178184645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637185471662876118789763 2455778207494314178184645)
                ·
                  refine ⟨460458413905183908409621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455778207494314178184645 460458413905183908409621)
                  ·
                    refine ⟨21583988151805495706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 460458413905183908409621 21583988151805495706701)
                    ·
                      refine ⟨8093995556927060890013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21583988151805495706701 8093995556927060890013)
                      ·
                        rfl

theorem cell23_15763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_15763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15763 prefixEnd_15763 := by exact prefixLift 15763
  have htrace : WordTrace (prefixWord ++ tailWord_15763) baseStart_15763 baseEnd_15763 := by
    simpa [prefixWord, tailWord_15763, baseEnd_15763] using wordTrace_append hprefix tailTrace_15763
  have hstable : (prefixWord ++ tailWord_15763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15763).length < 2 ^ (prefixWord ++ tailWord_15763).sum := by decide
  have hdescent : baseEnd_15763 < baseStart_15763 := by decide
  rcases family_descends (prefixWord ++ tailWord_15763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15770 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_15770 : Nat := 118140960795 + 15770 * 2 ^ 59
def prefixEnd_15770 : Nat := 4983230072969 + 3 ^ 40 * 15770 * 2
def baseEnd_15770 : Nat := 2699196640502844500827

theorem tailTrace_15770 : CollatzResearch.WordTrace tailWord_15770 prefixEnd_15770 2699196640502844500827 := by
  unfold tailWord_15770
  simp only [CollatzResearch.WordTrace]
  refine ⟨143794788218864536671191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 383452768583638764456509 143794788218864536671191)
  ·
    refine ⟨215692182328296805006787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143794788218864536671191 215692182328296805006787)
    ·
      refine ⟨323538273492445207510181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215692182328296805006787 323538273492445207510181)
      ·
        refine ⟨60663426279833476408159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 323538273492445207510181 60663426279833476408159)
        ·
          refine ⟨90995139419750214612239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60663426279833476408159 90995139419750214612239)
          ·
            refine ⟨136492709129625321918359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90995139419750214612239 136492709129625321918359)
            ·
              refine ⟨204739063694437982877539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136492709129625321918359 204739063694437982877539)
              ·
                refine ⟨307108595541656974316309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204739063694437982877539 307108595541656974316309)
                ·
                  refine ⟨14395715416015170671077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 307108595541656974316309 14395715416015170671077)
                  ·
                    refine ⟨2699196640502844500827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14395715416015170671077 2699196640502844500827)
                    ·
                      rfl

theorem cell23_15770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_15770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15770 prefixEnd_15770 := by exact prefixLift 15770
  have htrace : WordTrace (prefixWord ++ tailWord_15770) baseStart_15770 baseEnd_15770 := by
    simpa [prefixWord, tailWord_15770, baseEnd_15770] using wordTrace_append hprefix tailTrace_15770
  have hstable : (prefixWord ++ tailWord_15770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15770).length < 2 ^ (prefixWord ++ tailWord_15770).sum := by decide
  have hdescent : baseEnd_15770 < baseStart_15770 := by decide
  rcases family_descends (prefixWord ++ tailWord_15770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15780 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_15780 : Nat := 118140960795 + 15780 * 2 ^ 59
def prefixEnd_15780 : Nat := 4983230072969 + 3 ^ 40 * 15780 * 2
def baseEnd_15780 : Nat := 8102724728053494377435

theorem tailTrace_15780 : CollatzResearch.WordTrace tailWord_15780 prefixEnd_15780 8102724728053494377435 := by
  unfold tailWord_15780
  simp only [CollatzResearch.WordTrace]
  refine ⟨287771941419614927274397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 383695921892819903032529 287771941419614927274397)
  ·
    refine ⟨107914478032355597727899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 287771941419614927274397 107914478032355597727899)
    ·
      refine ⟨161871717048533396591849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107914478032355597727899 161871717048533396591849)
      ·
        refine ⟨121403787786400047443887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161871717048533396591849 121403787786400047443887)
        ·
          refine ⟨182105681679600071165831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121403787786400047443887 182105681679600071165831)
          ·
            refine ⟨273158522519400106748747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182105681679600071165831 273158522519400106748747)
            ·
              refine ⟨409737783779100160123121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273158522519400106748747 409737783779100160123121)
              ·
                refine ⟨307303337834325120092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409737783779100160123121 307303337834325120092341)
                ·
                  refine ⟨28809687921967980008657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307303337834325120092341 28809687921967980008657)
                  ·
                    refine ⟨21607265941475985006493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28809687921967980008657 21607265941475985006493)
                    ·
                      refine ⟨8102724728053494377435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21607265941475985006493 8102724728053494377435)
                      ·
                        rfl

theorem cell23_15780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_15780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15780 prefixEnd_15780 := by exact prefixLift 15780
  have htrace : WordTrace (prefixWord ++ tailWord_15780) baseStart_15780 baseEnd_15780 := by
    simpa [prefixWord, tailWord_15780, baseEnd_15780] using wordTrace_append hprefix tailTrace_15780
  have hstable : (prefixWord ++ tailWord_15780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15780).length < 2 ^ (prefixWord ++ tailWord_15780).sum := by decide
  have hdescent : baseEnd_15780 < baseStart_15780 := by decide
  rcases family_descends (prefixWord ++ tailWord_15780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15804 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_15804 : Nat := 118140960795 + 15804 * 2 ^ 59
def prefixEnd_15804 : Nat := 4983230072969 + 3 ^ 40 * 15804 * 2
def baseEnd_15804 : Nat := 2705016087920466825775

theorem tailTrace_15804 : CollatzResearch.WordTrace tailWord_15804 prefixEnd_15804 2705016087920466825775 := by
  unfold tailWord_15804
  simp only [CollatzResearch.WordTrace]
  refine ⟨288209617376140976711233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 384279489834854635614977 288209617376140976711233)
  ·
    refine ⟨216157213032105732533425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288209617376140976711233 216157213032105732533425)
    ·
      refine ⟨162117909774079299400069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216157213032105732533425 162117909774079299400069)
      ·
        refine ⟨30397108082639868637513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 162117909774079299400069 30397108082639868637513)
        ·
          refine ⟨22797831061979901478135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30397108082639868637513 22797831061979901478135)
          ·
            refine ⟨34196746592969852217203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22797831061979901478135 34196746592969852217203)
            ·
              refine ⟨51295119889454778325805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34196746592969852217203 51295119889454778325805)
              ·
                refine ⟨19235669958545541872177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51295119889454778325805 19235669958545541872177)
                ·
                  refine ⟨14426752468909156404133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19235669958545541872177 14426752468909156404133)
                  ·
                    refine ⟨2705016087920466825775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14426752468909156404133 2705016087920466825775)
                    ·
                      rfl

theorem cell23_15804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_15804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15804 prefixEnd_15804 := by exact prefixLift 15804
  have htrace : WordTrace (prefixWord ++ tailWord_15804) baseStart_15804 baseEnd_15804 := by
    simpa [prefixWord, tailWord_15804, baseEnd_15804] using wordTrace_append hprefix tailTrace_15804
  have hstable : (prefixWord ++ tailWord_15804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15804).length < 2 ^ (prefixWord ++ tailWord_15804).sum := by decide
  have hdescent : baseEnd_15804 < baseStart_15804 := by decide
  rcases family_descends (prefixWord ++ tailWord_15804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15823 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_15823 : Nat := 118140960795 + 15823 * 2 ^ 59
def prefixEnd_15823 : Nat := 4983230072969 + 3 ^ 40 * 15823 * 2
def baseEnd_15823 : Nat := 8124804396196826139737

theorem tailTrace_15823 : CollatzResearch.WordTrace tailWord_15823 prefixEnd_15823 8124804396196826139737 := by
  unfold tailWord_15823
  simp only [CollatzResearch.WordTrace]
  refine ⟨577112221683448198364123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 384741481122298798909415 577112221683448198364123)
  ·
    refine ⟨865668332525172297546185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577112221683448198364123 865668332525172297546185)
    ·
      refine ⟨649251249393879223159639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 865668332525172297546185 649251249393879223159639)
      ·
        refine ⟨973876874090818834739459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649251249393879223159639 973876874090818834739459)
        ·
          refine ⟨1460815311136228252109189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973876874090818834739459 1460815311136228252109189)
          ·
            refine ⟨273902870838042797270473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1460815311136228252109189 273902870838042797270473)
            ·
              refine ⟨205427153128532097952855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273902870838042797270473 205427153128532097952855)
              ·
                refine ⟨308140729692798146929283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205427153128532097952855 308140729692798146929283)
                ·
                  refine ⟨462211094539197220393925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308140729692798146929283 462211094539197220393925)
                  ·
                    refine ⟨86664580226099478823861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462211094539197220393925 86664580226099478823861)
                    ·
                      refine ⟨8124804396196826139737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 86664580226099478823861 8124804396196826139737)
                      ·
                        rfl

theorem cell23_15823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_15823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15823 prefixEnd_15823 := by exact prefixLift 15823
  have htrace : WordTrace (prefixWord ++ tailWord_15823) baseStart_15823 baseEnd_15823 := by
    simpa [prefixWord, tailWord_15823, baseEnd_15823] using wordTrace_append hprefix tailTrace_15823
  have hstable : (prefixWord ++ tailWord_15823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15823).length < 2 ^ (prefixWord ++ tailWord_15823).sum := by decide
  have hdescent : baseEnd_15823 < baseStart_15823 := by decide
  rcases family_descends (prefixWord ++ tailWord_15823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15845 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_15845 : Nat := 118140960795 + 15845 * 2 ^ 59
def prefixEnd_15845 : Nat := 4983230072969 + 3 ^ 40 * 15845 * 2
def baseEnd_15845 : Nat := 8136100970595740064637

theorem tailTrace_15845 : CollatzResearch.WordTrace tailWord_15845 prefixEnd_15845 8136100970595740064637 := by
  unfold tailWord_15845
  simp only [CollatzResearch.WordTrace]
  refine ⟨577914627603745955664989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385276418402497303776659 577914627603745955664989)
  ·
    refine ⟨216717985351404733374371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 577914627603745955664989 216717985351404733374371)
    ·
      refine ⟨325076978027107100061557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216717985351404733374371 325076978027107100061557)
      ·
        refine ⟨30475966690041290630771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 325076978027107100061557 30475966690041290630771)
        ·
          refine ⟨45713950035061935946157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30475966690041290630771 45713950035061935946157)
          ·
            refine ⟨17142731263148225979809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45713950035061935946157 17142731263148225979809)
            ·
              refine ⟨12857048447361169484857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17142731263148225979809 12857048447361169484857)
              ·
                refine ⟨9642786335520877113643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12857048447361169484857 9642786335520877113643)
                ·
                  refine ⟨14464179503281315670465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9642786335520877113643 14464179503281315670465)
                  ·
                    refine ⟨10848134627460986752849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14464179503281315670465 10848134627460986752849)
                    ·
                      refine ⟨8136100970595740064637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 10848134627460986752849 8136100970595740064637)
                      ·
                        rfl

theorem cell23_15845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_15845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15845 prefixEnd_15845 := by exact prefixLift 15845
  have htrace : WordTrace (prefixWord ++ tailWord_15845) baseStart_15845 baseEnd_15845 := by
    simpa [prefixWord, tailWord_15845, baseEnd_15845] using wordTrace_append hprefix tailTrace_15845
  have hstable : (prefixWord ++ tailWord_15845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15845).length < 2 ^ (prefixWord ++ tailWord_15845).sum := by decide
  have hdescent : baseEnd_15845 < baseStart_15845 := by decide
  rcases family_descends (prefixWord ++ tailWord_15845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15861 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_15861 : Nat := 118140960795 + 15861 * 2 ^ 59
def prefixEnd_15861 : Nat := 4983230072969 + 3 ^ 40 * 15861 * 2
def baseEnd_15861 : Nat := 8144316661067677464563

theorem tailTrace_15861 : CollatzResearch.WordTrace tailWord_15861 prefixEnd_15861 8144316661067677464563 := by
  unfold tailWord_15861
  simp only [CollatzResearch.WordTrace]
  refine ⟨578498195545780688247437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385665463697187125498291 578498195545780688247437)
  ·
    refine ⟨216936823329667758092789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 578498195545780688247437 216936823329667758092789)
    ·
      refine ⟨20337827187156352321199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 216936823329667758092789 20337827187156352321199)
      ·
        refine ⟨30506740780734528481799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20337827187156352321199 30506740780734528481799)
        ·
          refine ⟨45760111171101792722699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30506740780734528481799 45760111171101792722699)
          ·
            refine ⟨68640166756652689084049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45760111171101792722699 68640166756652689084049)
            ·
              refine ⟨51480125067489516813037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68640166756652689084049 51480125067489516813037)
              ·
                refine ⟨19305046900308568804889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51480125067489516813037 19305046900308568804889)
                ·
                  refine ⟨14478785175231426603667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19305046900308568804889 14478785175231426603667)
                  ·
                    refine ⟨21718177762847139905501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14478785175231426603667 21718177762847139905501)
                    ·
                      refine ⟨8144316661067677464563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21718177762847139905501 8144316661067677464563)
                      ·
                        rfl

theorem cell23_15861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_15861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15861 prefixEnd_15861 := by exact prefixLift 15861
  have htrace : WordTrace (prefixWord ++ tailWord_15861) baseStart_15861 baseEnd_15861 := by
    simpa [prefixWord, tailWord_15861, baseEnd_15861] using wordTrace_append hprefix tailTrace_15861
  have hstable : (prefixWord ++ tailWord_15861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15861).length < 2 ^ (prefixWord ++ tailWord_15861).sum := by decide
  have hdescent : baseEnd_15861 < baseStart_15861 := by decide
  rcases family_descends (prefixWord ++ tailWord_15861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15907 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 7]
def baseStart_15907 : Nat := 118140960795 + 15907 * 2 ^ 59
def prefixEnd_15907 : Nat := 4983230072969 + 3 ^ 40 * 15907 * 2
def baseEnd_15907 : Nat := 907548530130499721039

theorem tailTrace_15907 : CollatzResearch.WordTrace tailWord_15907 prefixEnd_15907 907548530130499721039 := by
  unfold tailWord_15907
  simp only [CollatzResearch.WordTrace]
  refine ⟨580175953379130544421975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 386783968919420362947983 580175953379130544421975)
  ·
    refine ⟨870263930068695816632963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580175953379130544421975 870263930068695816632963)
    ·
      refine ⟨1305395895103043724949445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870263930068695816632963 1305395895103043724949445)
      ·
        refine ⟨244761730331820698428021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1305395895103043724949445 244761730331820698428021)
        ·
          refine ⟨22946412218608190477627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244761730331820698428021 22946412218608190477627)
          ·
            refine ⟨34419618327912285716441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22946412218608190477627 34419618327912285716441)
            ·
              refine ⟨25814713745934214287331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34419618327912285716441 25814713745934214287331)
              ·
                refine ⟨38722070618901321430997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25814713745934214287331 38722070618901321430997)
                ·
                  refine ⟨907548530130499721039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38722070618901321430997 907548530130499721039)
                  ·
                    rfl

theorem cell23_15907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 7].length) (baseStart_15907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15907 prefixEnd_15907 := by exact prefixLift 15907
  have htrace : WordTrace (prefixWord ++ tailWord_15907) baseStart_15907 baseEnd_15907 := by
    simpa [prefixWord, tailWord_15907, baseEnd_15907] using wordTrace_append hprefix tailTrace_15907
  have hstable : (prefixWord ++ tailWord_15907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15907).length < 2 ^ (prefixWord ++ tailWord_15907).sum := by decide
  have hdescent : baseEnd_15907 < baseStart_15907 := by decide
  rcases family_descends (prefixWord ++ tailWord_15907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15937 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 2, 5]
def baseStart_15937 : Nat := 118140960795 + 15937 * 2 ^ 59
def prefixEnd_15937 : Nat := 4983230072969 + 3 ^ 40 * 15937 * 2
def baseEnd_15937 : Nat := 2727780396936460038071

theorem tailTrace_15937 : CollatzResearch.WordTrace tailWord_15937 prefixEnd_15937 2727780396936460038071 := by
  unfold tailWord_15937
  simp only [CollatzResearch.WordTrace]
  refine ⟨581270143270445668014065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 387513428846963778676043 581270143270445668014065)
  ·
    refine ⟨435952607452834251010549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 581270143270445668014065 435952607452834251010549)
    ·
      refine ⟨40870556948703211032239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435952607452834251010549 40870556948703211032239)
      ·
        refine ⟨61305835423054816548359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40870556948703211032239 61305835423054816548359)
        ·
          refine ⟨91958753134582224822539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61305835423054816548359 91958753134582224822539)
          ·
            refine ⟨137938129701873337233809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91958753134582224822539 137938129701873337233809)
            ·
              refine ⟨103453597276405002925357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137938129701873337233809 103453597276405002925357)
              ·
                refine ⟨38795098978651876097009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103453597276405002925357 38795098978651876097009)
                ·
                  refine ⟨29096324233988907072757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38795098978651876097009 29096324233988907072757)
                  ·
                    refine ⟨2727780396936460038071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29096324233988907072757 2727780396936460038071)
                    ·
                      rfl

theorem cell23_15937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_15937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15937 prefixEnd_15937 := by exact prefixLift 15937
  have htrace : WordTrace (prefixWord ++ tailWord_15937) baseStart_15937 baseEnd_15937 := by
    simpa [prefixWord, tailWord_15937, baseEnd_15937] using wordTrace_append hprefix tailTrace_15937
  have hstable : (prefixWord ++ tailWord_15937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15937).length < 2 ^ (prefixWord ++ tailWord_15937).sum := by decide
  have hdescent : baseEnd_15937 < baseStart_15937 := by decide
  rcases family_descends (prefixWord ++ tailWord_15937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15958 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_15958 : Nat := 118140960795 + 15958 * 2 ^ 59
def prefixEnd_15958 : Nat := 4983230072969 + 3 ^ 40 * 15958 * 2
def baseEnd_15958 : Nat := 910458253839310883513

theorem tailTrace_15958 : CollatzResearch.WordTrace tailWord_15958 prefixEnd_15958 910458253839310883513 := by
  unfold tailWord_15958
  simp only [CollatzResearch.WordTrace]
  refine ⟨36377254762147890908033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 388024050796244169685685 36377254762147890908033)
  ·
    refine ⟨27282941071610918181025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36377254762147890908033 27282941071610918181025)
    ·
      refine ⟨20462205803708188635769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27282941071610918181025 20462205803708188635769)
      ·
        refine ⟨15346654352781141476827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20462205803708188635769 15346654352781141476827)
        ·
          refine ⟨23019981529171712215241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15346654352781141476827 23019981529171712215241)
          ·
            refine ⟨17264986146878784161431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23019981529171712215241 17264986146878784161431)
            ·
              refine ⟨25897479220318176242147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17264986146878784161431 25897479220318176242147)
              ·
                refine ⟨38846218830477264363221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25897479220318176242147 38846218830477264363221)
                ·
                  refine ⟨910458253839310883513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38846218830477264363221 910458253839310883513)
                  ·
                    rfl

theorem cell23_15958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_15958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_15958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_15958 prefixEnd_15958 := by exact prefixLift 15958
  have htrace : WordTrace (prefixWord ++ tailWord_15958) baseStart_15958 baseEnd_15958 := by
    simpa [prefixWord, tailWord_15958, baseEnd_15958] using wordTrace_append hprefix tailTrace_15958
  have hstable : (prefixWord ++ tailWord_15958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15958).length < 2 ^ (prefixWord ++ tailWord_15958).sum := by decide
  have hdescent : baseEnd_15958 < baseStart_15958 := by decide
  rcases family_descends (prefixWord ++ tailWord_15958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16014 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_16014 : Nat := 118140960795 + 16014 * 2 ^ 59
def prefixEnd_16014 : Nat := 4983230072969 + 3 ^ 40 * 16014 * 2
def baseEnd_16014 : Nat := 913653244578397650151

theorem tailTrace_16014 : CollatzResearch.WordTrace tailWord_16014 prefixEnd_16014 913653244578397650151 := by
  unfold tailWord_16014
  simp only [CollatzResearch.WordTrace]
  refine ⟨73009820498935977320887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 389385709327658545711397 73009820498935977320887)
  ·
    refine ⟨109514730748403965981331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73009820498935977320887 109514730748403965981331)
    ·
      refine ⟨164272096122605948971997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109514730748403965981331 164272096122605948971997)
      ·
        refine ⟨61602036045977230864499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164272096122605948971997 61602036045977230864499)
        ·
          refine ⟨92403054068965846296749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61602036045977230864499 92403054068965846296749)
          ·
            refine ⟨34651145275862192361281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92403054068965846296749 34651145275862192361281)
            ·
              refine ⟨25988358956896644270961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34651145275862192361281 25988358956896644270961)
              ·
                refine ⟨19491269217672483203221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25988358956896644270961 19491269217672483203221)
                ·
                  refine ⟨913653244578397650151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19491269217672483203221 913653244578397650151)
                  ·
                    rfl

theorem cell23_16014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_16014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16014 prefixEnd_16014 := by exact prefixLift 16014
  have htrace : WordTrace (prefixWord ++ tailWord_16014) baseStart_16014 baseEnd_16014 := by
    simpa [prefixWord, tailWord_16014, baseEnd_16014] using wordTrace_append hprefix tailTrace_16014
  have hstable : (prefixWord ++ tailWord_16014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16014).length < 2 ^ (prefixWord ++ tailWord_16014).sum := by decide
  have hdescent : baseEnd_16014 < baseStart_16014 := by decide
  rcases family_descends (prefixWord ++ tailWord_16014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16018 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_16018 : Nat := 118140960795 + 16018 * 2 ^ 59
def prefixEnd_16018 : Nat := 4983230072969 + 3 ^ 40 * 16018 * 2
def baseEnd_16018 : Nat := 2741644374607854400447

theorem tailTrace_16018 : CollatzResearch.WordTrace tailWord_16018 prefixEnd_16018 2741644374607854400447 := by
  unfold tailWord_16018
  simp only [CollatzResearch.WordTrace]
  refine ⟨146056113994249125428177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 389482970651331001141805 146056113994249125428177)
  ·
    refine ⟨109542085495686844071133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146056113994249125428177 109542085495686844071133)
    ·
      refine ⟨41078282060882566526675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109542085495686844071133 41078282060882566526675)
      ·
        refine ⟨61617423091323849790013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41078282060882566526675 61617423091323849790013)
        ·
          refine ⟨23106533659246443671255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61617423091323849790013 23106533659246443671255)
          ·
            refine ⟨34659800488869665506883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23106533659246443671255 34659800488869665506883)
            ·
              refine ⟨51989700733304498260325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34659800488869665506883 51989700733304498260325)
              ·
                refine ⟨9748068887494593423811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51989700733304498260325 9748068887494593423811)
                ·
                  refine ⟨14622103331241890135717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748068887494593423811 14622103331241890135717)
                  ·
                    refine ⟨2741644374607854400447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14622103331241890135717 2741644374607854400447)
                    ·
                      rfl

theorem cell23_16018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_16018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16018 prefixEnd_16018 := by exact prefixLift 16018
  have htrace : WordTrace (prefixWord ++ tailWord_16018) baseStart_16018 baseEnd_16018 := by
    simpa [prefixWord, tailWord_16018, baseEnd_16018] using wordTrace_append hprefix tailTrace_16018
  have hstable : (prefixWord ++ tailWord_16018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16018).length < 2 ^ (prefixWord ++ tailWord_16018).sum := by decide
  have hdescent : baseEnd_16018 < baseStart_16018 := by decide
  rcases family_descends (prefixWord ++ tailWord_16018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16047 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_16047 : Nat := 118140960795 + 16047 * 2 ^ 59
def prefixEnd_16047 : Nat := 4983230072969 + 3 ^ 40 * 16047 * 2
def baseEnd_16047 : Nat := 8239824062803949738707

theorem tailTrace_16047 : CollatzResearch.WordTrace tailWord_16047 prefixEnd_16047 8239824062803949738707 := by
  unfold tailWord_16047
  simp only [CollatzResearch.WordTrace]
  refine ⟨585282172871934454518395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 390188115247956303012263 585282172871934454518395)
  ·
    refine ⟨877923259307901681777593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585282172871934454518395 877923259307901681777593)
    ·
      refine ⟨658442444480926261333195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 877923259307901681777593 658442444480926261333195)
      ·
        refine ⟨987663666721389391999793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658442444480926261333195 987663666721389391999793)
        ·
          refine ⟨740747750041042043999845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 987663666721389391999793 740747750041042043999845)
          ·
            refine ⟨138890203132695383249971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 740747750041042043999845 138890203132695383249971)
            ·
              refine ⟨208335304699043074874957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138890203132695383249971 208335304699043074874957)
              ·
                refine ⟨78125739262141153078109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208335304699043074874957 78125739262141153078109)
                ·
                  refine ⟨29297152223302932404291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78125739262141153078109 29297152223302932404291)
                  ·
                    refine ⟨43945728334954398606437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29297152223302932404291 43945728334954398606437)
                    ·
                      refine ⟨8239824062803949738707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 43945728334954398606437 8239824062803949738707)
                      ·
                        rfl

theorem cell23_16047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_16047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16047 prefixEnd_16047 := by exact prefixLift 16047
  have htrace : WordTrace (prefixWord ++ tailWord_16047) baseStart_16047 baseEnd_16047 := by
    simpa [prefixWord, tailWord_16047, baseEnd_16047] using wordTrace_append hprefix tailTrace_16047
  have hstable : (prefixWord ++ tailWord_16047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16047).length < 2 ^ (prefixWord ++ tailWord_16047).sum := by decide
  have hdescent : baseEnd_16047 < baseStart_16047 := by decide
  rcases family_descends (prefixWord ++ tailWord_16047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16057 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 6]
def baseStart_16057 : Nat := 118140960795 + 16057 * 2 ^ 59
def prefixEnd_16057 : Nat := 4983230072969 + 3 ^ 40 * 16057 * 2
def baseEnd_16057 : Nat := 2748319623116303537887

theorem tailTrace_16057 : CollatzResearch.WordTrace tailWord_16057 prefixEnd_16057 2748319623116303537887 := by
  unfold tailWord_16057
  simp only [CollatzResearch.WordTrace]
  refine ⟨585646902835706162382425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 390431268557137441588283 585646902835706162382425)
  ·
    refine ⟨439235177126779621786819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 585646902835706162382425 439235177126779621786819)
    ·
      refine ⟨658852765690169432680229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439235177126779621786819 658852765690169432680229)
      ·
        refine ⟨123534893566906768627543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 658852765690169432680229 123534893566906768627543)
        ·
          refine ⟨185302340350360152941315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123534893566906768627543 185302340350360152941315)
          ·
            refine ⟨277953510525540229411973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185302340350360152941315 277953510525540229411973)
            ·
              refine ⟨52116283223538793014745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277953510525540229411973 52116283223538793014745)
              ·
                refine ⟨39087212417654094761059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52116283223538793014745 39087212417654094761059)
                ·
                  refine ⟨58630818626481142141589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39087212417654094761059 58630818626481142141589)
                  ·
                    refine ⟨2748319623116303537887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58630818626481142141589 2748319623116303537887)
                    ·
                      rfl

theorem cell23_16057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_16057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16057 prefixEnd_16057 := by exact prefixLift 16057
  have htrace : WordTrace (prefixWord ++ tailWord_16057) baseStart_16057 baseEnd_16057 := by
    simpa [prefixWord, tailWord_16057, baseEnd_16057] using wordTrace_append hprefix tailTrace_16057
  have hstable : (prefixWord ++ tailWord_16057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16057).length < 2 ^ (prefixWord ++ tailWord_16057).sum := by decide
  have hdescent : baseEnd_16057 < baseStart_16057 := by decide
  rcases family_descends (prefixWord ++ tailWord_16057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16058 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_16058 : Nat := 118140960795 + 16058 * 2 ^ 59
def prefixEnd_16058 : Nat := 4983230072969 + 3 ^ 40 * 16058 * 2
def baseEnd_16058 : Nat := 8245472350003406701157

theorem tailTrace_16058 : CollatzResearch.WordTrace tailWord_16058 prefixEnd_16058 8245472350003406701157 := by
  unfold tailWord_16058
  simp only [CollatzResearch.WordTrace]
  refine ⟨146420843958020833292207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 390455583888055555445885 146420843958020833292207)
  ·
    refine ⟨219631265937031249938311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146420843958020833292207 219631265937031249938311)
    ·
      refine ⟨329446898905546874907467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219631265937031249938311 329446898905546874907467)
      ·
        refine ⟨494170348358320312361201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329446898905546874907467 494170348358320312361201)
        ·
          refine ⟨370627761268740234270901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494170348358320312361201 370627761268740234270901)
          ·
            refine ⟨34746352618944396962897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 370627761268740234270901 34746352618944396962897)
            ·
              refine ⟨26059764464208297722173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34746352618944396962897 26059764464208297722173)
              ·
                refine ⟨9772411674078111645815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26059764464208297722173 9772411674078111645815)
                ·
                  refine ⟨14658617511117167468723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9772411674078111645815 14658617511117167468723)
                  ·
                    refine ⟨21987926266675751203085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14658617511117167468723 21987926266675751203085)
                    ·
                      refine ⟨8245472350003406701157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 21987926266675751203085 8245472350003406701157)
                      ·
                        rfl

theorem cell23_16058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_16058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16058 prefixEnd_16058 := by exact prefixLift 16058
  have htrace : WordTrace (prefixWord ++ tailWord_16058) baseStart_16058 baseEnd_16058 := by
    simpa [prefixWord, tailWord_16058, baseEnd_16058] using wordTrace_append hprefix tailTrace_16058
  have hstable : (prefixWord ++ tailWord_16058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16058).length < 2 ^ (prefixWord ++ tailWord_16058).sum := by decide
  have hdescent : baseEnd_16058 < baseStart_16058 := by decide
  rcases family_descends (prefixWord ++ tailWord_16058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16064 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_16064 : Nat := 118140960795 + 16064 * 2 ^ 59
def prefixEnd_16064 : Nat := 4983230072969 + 3 ^ 40 * 16064 * 2
def baseEnd_16064 : Nat := 8248553233930383226129

theorem tailTrace_16064 : CollatzResearch.WordTrace tailWord_16064 prefixEnd_16064 8248553233930383226129 := by
  unfold tailWord_16064
  simp only [CollatzResearch.WordTrace]
  refine ⟨292951106905173178943623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 390601475873564238591497 292951106905173178943623)
  ·
    refine ⟨439426660357759768415435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292951106905173178943623 439426660357759768415435)
    ·
      refine ⟨659139990536639652623153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439426660357759768415435 659139990536639652623153)
      ·
        refine ⟨494354992902479739467365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659139990536639652623153 494354992902479739467365)
        ·
          refine ⟨92691561169214951150131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494354992902479739467365 92691561169214951150131)
          ·
            refine ⟨139037341753822426725197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92691561169214951150131 139037341753822426725197)
            ·
              refine ⟨52139003157683410021949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139037341753822426725197 52139003157683410021949)
              ·
                refine ⟨19552126184131278758231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52139003157683410021949 19552126184131278758231)
                ·
                  refine ⟨29328189276196918137347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19552126184131278758231 29328189276196918137347)
                  ·
                    refine ⟨43992283914295377206021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29328189276196918137347 43992283914295377206021)
                    ·
                      refine ⟨8248553233930383226129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 43992283914295377206021 8248553233930383226129)
                      ·
                        rfl

theorem cell23_16064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_16064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16064 prefixEnd_16064 := by exact prefixLift 16064
  have htrace : WordTrace (prefixWord ++ tailWord_16064) baseStart_16064 baseEnd_16064 := by
    simpa [prefixWord, tailWord_16064, baseEnd_16064] using wordTrace_append hprefix tailTrace_16064
  have hstable : (prefixWord ++ tailWord_16064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16064).length < 2 ^ (prefixWord ++ tailWord_16064).sum := by decide
  have hdescent : baseEnd_16064 < baseStart_16064 := by decide
  rcases family_descends (prefixWord ++ tailWord_16064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16081 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_16081 : Nat := 118140960795 + 16081 * 2 ^ 59
def prefixEnd_16081 : Nat := 4983230072969 + 3 ^ 40 * 16081 * 2
def baseEnd_16081 : Nat := 8257282405056816713551

theorem tailTrace_16081 : CollatzResearch.WordTrace tailWord_16081 prefixEnd_16081 8257282405056816713551 := by
  unfold tailWord_16081
  simp only [CollatzResearch.WordTrace]
  refine ⟨586522254748758261256097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 391014836499172174170731 586522254748758261256097)
  ·
    refine ⟨439891691061568695942073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586522254748758261256097 439891691061568695942073)
    ·
      refine ⟨329918768296176521956555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439891691061568695942073 329918768296176521956555)
      ·
        refine ⟨494878152444264782934833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329918768296176521956555 494878152444264782934833)
        ·
          refine ⟨371158614333198587201125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494878152444264782934833 371158614333198587201125)
          ·
            refine ⟨69592240187474735100211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371158614333198587201125 69592240187474735100211)
            ·
              refine ⟨104388360281212102650317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69592240187474735100211 104388360281212102650317)
              ·
                refine ⟨39145635105454538493869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104388360281212102650317 39145635105454538493869)
                ·
                  refine ⟨14679613164545451935201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39145635105454538493869 14679613164545451935201)
                  ·
                    refine ⟨11009709873409088951401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679613164545451935201 11009709873409088951401)
                    ·
                      refine ⟨8257282405056816713551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11009709873409088951401 8257282405056816713551)
                      ·
                        rfl

theorem cell23_16081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_16081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16081 prefixEnd_16081 := by exact prefixLift 16081
  have htrace : WordTrace (prefixWord ++ tailWord_16081) baseStart_16081 baseEnd_16081 := by
    simpa [prefixWord, tailWord_16081, baseEnd_16081] using wordTrace_append hprefix tailTrace_16081
  have hstable : (prefixWord ++ tailWord_16081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16081).length < 2 ^ (prefixWord ++ tailWord_16081).sum := by decide
  have hdescent : baseEnd_16081 < baseStart_16081 := by decide
  rcases family_descends (prefixWord ++ tailWord_16081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16084 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_16084 : Nat := 118140960795 + 16084 * 2 ^ 59
def prefixEnd_16084 : Nat := 4983230072969 + 3 ^ 40 * 16084 * 2
def baseEnd_16084 : Nat := 8258822847020304976037

theorem tailTrace_16084 : CollatzResearch.WordTrace tailWord_16084 prefixEnd_16084 8258822847020304976037 := by
  unfold tailWord_16084
  simp only [CollatzResearch.WordTrace]
  refine ⟨293315836868944886807653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 391087782491926515743537 293315836868944886807653)
  ·
    refine ⟨54996719412927166276435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293315836868944886807653 54996719412927166276435)
    ·
      refine ⟨82495079119390749414653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54996719412927166276435 82495079119390749414653)
      ·
        refine ⟨30935654669771531030495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82495079119390749414653 30935654669771531030495)
        ·
          refine ⟨46403482004657296545743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30935654669771531030495 46403482004657296545743)
          ·
            refine ⟨69605223006985944818615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46403482004657296545743 69605223006985944818615)
            ·
              refine ⟨104407834510478917227923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69605223006985944818615 104407834510478917227923)
              ·
                refine ⟨156611751765718375841885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104407834510478917227923 156611751765718375841885)
                ·
                  refine ⟨58729406912144390940707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156611751765718375841885 58729406912144390940707)
                  ·
                    refine ⟨88094110368216586411061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58729406912144390940707 88094110368216586411061)
                    ·
                      refine ⟨8258822847020304976037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 88094110368216586411061 8258822847020304976037)
                      ·
                        rfl

theorem cell23_16084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_16084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16084 prefixEnd_16084 := by exact prefixLift 16084
  have htrace : WordTrace (prefixWord ++ tailWord_16084) baseStart_16084 baseEnd_16084 := by
    simpa [prefixWord, tailWord_16084, baseEnd_16084] using wordTrace_append hprefix tailTrace_16084
  have hstable : (prefixWord ++ tailWord_16084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16084).length < 2 ^ (prefixWord ++ tailWord_16084).sum := by decide
  have hdescent : baseEnd_16084 < baseStart_16084 := by decide
  rcases family_descends (prefixWord ++ tailWord_16084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16101 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_16101 : Nat := 118140960795 + 16101 * 2 ^ 59
def prefixEnd_16101 : Nat := 4983230072969 + 3 ^ 40 * 16101 * 2
def baseEnd_16101 : Nat := 8267552018146738463459

theorem tailTrace_16101 : CollatzResearch.WordTrace tailWord_16101 prefixEnd_16101 8267552018146738463459 := by
  unfold tailWord_16101
  simp only [CollatzResearch.WordTrace]
  refine ⟨587251714676301676984157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 391501143117534451322771 587251714676301676984157)
  ·
    refine ⟨220219393003613128869059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 587251714676301676984157 220219393003613128869059)
    ·
      refine ⟨330329089505419693303589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220219393003613128869059 330329089505419693303589)
      ·
        refine ⟨61936704282266192494423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330329089505419693303589 61936704282266192494423)
        ·
          refine ⟨92905056423399288741635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61936704282266192494423 92905056423399288741635)
          ·
            refine ⟨139357584635098933112453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92905056423399288741635 139357584635098933112453)
            ·
              refine ⟨26129547119081049958585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139357584635098933112453 26129547119081049958585)
              ·
                refine ⟨19597160339310787468939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26129547119081049958585 19597160339310787468939)
                ·
                  refine ⟨29395740508966181203409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19597160339310787468939 29395740508966181203409)
                  ·
                    refine ⟨22046805381724635902557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29395740508966181203409 22046805381724635902557)
                    ·
                      refine ⟨8267552018146738463459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22046805381724635902557 8267552018146738463459)
                      ·
                        rfl

theorem cell23_16101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_16101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16101 prefixEnd_16101 := by exact prefixLift 16101
  have htrace : WordTrace (prefixWord ++ tailWord_16101) baseStart_16101 baseEnd_16101 := by
    simpa [prefixWord, tailWord_16101, baseEnd_16101] using wordTrace_append hprefix tailTrace_16101
  have hstable : (prefixWord ++ tailWord_16101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16101).length < 2 ^ (prefixWord ++ tailWord_16101).sum := by decide
  have hdescent : baseEnd_16101 < baseStart_16101 := by decide
  rcases family_descends (prefixWord ++ tailWord_16101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16104 : List Nat := [2, 1, 4, 1, 3, 1, 4, 7]
def baseStart_16104 : Nat := 118140960795 + 16104 * 2 ^ 59
def prefixEnd_16104 : Nat := 4983230072969 + 3 ^ 40 * 16104 * 2
def baseEnd_16104 : Nat := 306262683707786175035

theorem tailTrace_16104 : CollatzResearch.WordTrace tailWord_16104 prefixEnd_16104 306262683707786175035 := by
  unfold tailWord_16104
  simp only [CollatzResearch.WordTrace]
  refine ⟨293680566832716594671683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 391574089110288792895577 293680566832716594671683)
  ·
    refine ⟨440520850249074892007525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293680566832716594671683 440520850249074892007525)
    ·
      refine ⟨82597659421701542251411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440520850249074892007525 82597659421701542251411)
      ·
        refine ⟨123896489132552313377117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82597659421701542251411 123896489132552313377117)
        ·
          refine ⟨46461183424707117516419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123896489132552313377117 46461183424707117516419)
          ·
            refine ⟨69691775137060676274629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46461183424707117516419 69691775137060676274629)
            ·
              refine ⟨13067207838198876801493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69691775137060676274629 13067207838198876801493)
              ·
                refine ⟨306262683707786175035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13067207838198876801493 306262683707786175035)
                ·
                  rfl

theorem cell23_16104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 7].length) (baseStart_16104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16104 prefixEnd_16104 := by exact prefixLift 16104
  have htrace : WordTrace (prefixWord ++ tailWord_16104) baseStart_16104 baseEnd_16104 := by
    simpa [prefixWord, tailWord_16104, baseEnd_16104] using wordTrace_append hprefix tailTrace_16104
  have hstable : (prefixWord ++ tailWord_16104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16104).length < 2 ^ (prefixWord ++ tailWord_16104).sum := by decide
  have hdescent : baseEnd_16104 < baseStart_16104 := by decide
  rcases family_descends (prefixWord ++ tailWord_16104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16114 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 3, 3]
def baseStart_16114 : Nat := 118140960795 + 16114 * 2 ^ 59
def prefixEnd_16114 : Nat := 4983230072969 + 3 ^ 40 * 16114 * 2
def baseEnd_16114 : Nat := 8274227266655187600899

theorem tailTrace_16114 : CollatzResearch.WordTrace tailWord_16114 prefixEnd_16114 8274227266655187600899 := by
  unfold tailWord_16114
  simp only [CollatzResearch.WordTrace]
  refine ⟨146931465907301224301849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 391817242419469931471597 146931465907301224301849)
  ·
    refine ⟨110198599430475918226387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146931465907301224301849 110198599430475918226387)
    ·
      refine ⟨165297899145713877339581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110198599430475918226387 165297899145713877339581)
      ·
        refine ⟨61986712179642704002343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165297899145713877339581 61986712179642704002343)
        ·
          refine ⟨92980068269464056003515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61986712179642704002343 92980068269464056003515)
          ·
            refine ⟨139470102404196084005273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92980068269464056003515 139470102404196084005273)
            ·
              refine ⟨104602576803147063003955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139470102404196084005273 104602576803147063003955)
              ·
                refine ⟨156903865204720594505933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104602576803147063003955 156903865204720594505933)
                ·
                  refine ⟨58838949451770222939725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156903865204720594505933 58838949451770222939725)
                  ·
                    refine ⟨22064606044413833602397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58838949451770222939725 22064606044413833602397)
                    ·
                      refine ⟨8274227266655187600899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22064606044413833602397 8274227266655187600899)
                      ·
                        rfl

theorem cell23_16114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_16114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16114 prefixEnd_16114 := by exact prefixLift 16114
  have htrace : WordTrace (prefixWord ++ tailWord_16114) baseStart_16114 baseEnd_16114 := by
    simpa [prefixWord, tailWord_16114, baseEnd_16114] using wordTrace_append hprefix tailTrace_16114
  have hstable : (prefixWord ++ tailWord_16114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16114).length < 2 ^ (prefixWord ++ tailWord_16114).sum := by decide
  have hdescent : baseEnd_16114 < baseStart_16114 := by decide
  rcases family_descends (prefixWord ++ tailWord_16114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16132 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_16132 : Nat := 118140960795 + 16132 * 2 ^ 59
def prefixEnd_16132 : Nat := 4983230072969 + 3 ^ 40 * 16132 * 2
def baseEnd_16132 : Nat := 8283469918436117175817

theorem tailTrace_16132 : CollatzResearch.WordTrace tailWord_16132 prefixEnd_16132 8283469918436117175817 := by
  unfold tailWord_16132
  simp only [CollatzResearch.WordTrace]
  refine ⟨294191188781996985681325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 392254918375995980908433 294191188781996985681325)
  ·
    refine ⟨110321695793248869630497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294191188781996985681325 110321695793248869630497)
    ·
      refine ⟨82741271844936652222873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110321695793248869630497 82741271844936652222873)
      ·
        refine ⟨62055953883702489167155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82741271844936652222873 62055953883702489167155)
        ·
          refine ⟨93083930825553733750733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62055953883702489167155 93083930825553733750733)
          ·
            refine ⟨34906474059582650156525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93083930825553733750733 34906474059582650156525)
            ·
              refine ⟨13089927772343493808697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34906474059582650156525 13089927772343493808697)
              ·
                refine ⟨9817445829257620356523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089927772343493808697 9817445829257620356523)
                ·
                  refine ⟨14726168743886430534785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817445829257620356523 14726168743886430534785)
                  ·
                    refine ⟨11044626557914822901089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14726168743886430534785 11044626557914822901089)
                    ·
                      refine ⟨8283469918436117175817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11044626557914822901089 8283469918436117175817)
                      ·
                        rfl

theorem cell23_16132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_16132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16132 prefixEnd_16132 := by exact prefixLift 16132
  have htrace : WordTrace (prefixWord ++ tailWord_16132) baseStart_16132 baseEnd_16132 := by
    simpa [prefixWord, tailWord_16132, baseEnd_16132] using wordTrace_append hprefix tailTrace_16132
  have hstable : (prefixWord ++ tailWord_16132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16132).length < 2 ^ (prefixWord ++ tailWord_16132).sum := by decide
  have hdescent : baseEnd_16132 < baseStart_16132 := by decide
  rcases family_descends (prefixWord ++ tailWord_16132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16137 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_16137 : Nat := 118140960795 + 16137 * 2 ^ 59
def prefixEnd_16137 : Nat := 4983230072969 + 3 ^ 40 * 16137 * 2
def baseEnd_16137 : Nat := 8286037321708597613293

theorem tailTrace_16137 : CollatzResearch.WordTrace tailWord_16137 prefixEnd_16137 8286037321708597613293 := by
  unfold tailWord_16137
  simp only [CollatzResearch.WordTrace]
  refine ⟨588564742545879825294665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 392376495030586550196443 588564742545879825294665)
  ·
    refine ⟨441423556909409868970999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 588564742545879825294665 441423556909409868970999)
    ·
      refine ⟨662135335364114803456499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441423556909409868970999 662135335364114803456499)
      ·
        refine ⟨993203003046172205184749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662135335364114803456499 993203003046172205184749)
        ·
          refine ⟨372451126142314576944281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993203003046172205184749 372451126142314576944281)
          ·
            refine ⟨279338344606735932708211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372451126142314576944281 279338344606735932708211)
            ·
              refine ⟨419007516910103899062317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279338344606735932708211 419007516910103899062317)
              ·
                refine ⟨157127818841288962148369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419007516910103899062317 157127818841288962148369)
                ·
                  refine ⟨117845864130966721611277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157127818841288962148369 117845864130966721611277)
                  ·
                    refine ⟨44192199049112520604229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117845864130966721611277 44192199049112520604229)
                    ·
                      refine ⟨8286037321708597613293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 44192199049112520604229 8286037321708597613293)
                      ·
                        rfl

theorem cell23_16137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_16137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16137 prefixEnd_16137 := by exact prefixLift 16137
  have htrace : WordTrace (prefixWord ++ tailWord_16137) baseStart_16137 baseEnd_16137 := by
    simpa [prefixWord, tailWord_16137, baseEnd_16137] using wordTrace_append hprefix tailTrace_16137
  have hstable : (prefixWord ++ tailWord_16137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16137).length < 2 ^ (prefixWord ++ tailWord_16137).sum := by decide
  have hdescent : baseEnd_16137 < baseStart_16137 := by decide
  rcases family_descends (prefixWord ++ tailWord_16137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16188 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_16188 : Nat := 118140960795 + 16188 * 2 ^ 59
def prefixEnd_16188 : Nat := 4983230072969 + 3 ^ 40 * 16188 * 2
def baseEnd_16188 : Nat := 8312224835087898075559

theorem tailTrace_16188 : CollatzResearch.WordTrace tailWord_16188 prefixEnd_16188 8312224835087898075559 := by
  unfold tailWord_16188
  simp only [CollatzResearch.WordTrace]
  refine ⟨295212432680557767700609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 393616576907410356934145 295212432680557767700609)
  ·
    refine ⟨221409324510418325775457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295212432680557767700609 221409324510418325775457)
    ·
      refine ⟨166056993382813744331593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221409324510418325775457 166056993382813744331593)
      ·
        refine ⟨124542745037110308248695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166056993382813744331593 124542745037110308248695)
        ·
          refine ⟨186814117555665462373043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124542745037110308248695 186814117555665462373043)
          ·
            refine ⟨280221176333498193559565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186814117555665462373043 280221176333498193559565)
            ·
              refine ⟨105082941125061822584837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280221176333498193559565 105082941125061822584837)
              ·
                refine ⟨19703051460949091734657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105082941125061822584837 19703051460949091734657)
                ·
                  refine ⟨14777288595711818800993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19703051460949091734657 14777288595711818800993)
                  ·
                    refine ⟨11082966446783864100745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14777288595711818800993 11082966446783864100745)
                    ·
                      refine ⟨8312224835087898075559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11082966446783864100745 8312224835087898075559)
                      ·
                        rfl

theorem cell23_16188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_16188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16188 prefixEnd_16188 := by exact prefixLift 16188
  have htrace : WordTrace (prefixWord ++ tailWord_16188) baseStart_16188 baseEnd_16188 := by
    simpa [prefixWord, tailWord_16188, baseEnd_16188] using wordTrace_append hprefix tailTrace_16188
  have hstable : (prefixWord ++ tailWord_16188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16188).length < 2 ^ (prefixWord ++ tailWord_16188).sum := by decide
  have hdescent : baseEnd_16188 < baseStart_16188 := by decide
  rcases family_descends (prefixWord ++ tailWord_16188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16198 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_16198 : Nat := 118140960795 + 16198 * 2 ^ 59
def prefixEnd_16198 : Nat := 4983230072969 + 3 ^ 40 * 16198 * 2
def baseEnd_16198 : Nat := 2772453213877619650171

theorem tailTrace_16198 : CollatzResearch.WordTrace tailWord_16198 prefixEnd_16198 2772453213877619650171 := by
  unfold tailWord_16198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462174853902726352039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 393859730216591495510165 18462174853902726352039)
  ·
    refine ⟨27693262280854089528059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18462174853902726352039 27693262280854089528059)
    ·
      refine ⟨41539893421281134292089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27693262280854089528059 41539893421281134292089)
      ·
        refine ⟨31154920065960850719067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41539893421281134292089 31154920065960850719067)
        ·
          refine ⟨46732380098941276078601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31154920065960850719067 46732380098941276078601)
          ·
            refine ⟨35049285074205957058951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46732380098941276078601 35049285074205957058951)
            ·
              refine ⟨52573927611308935588427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35049285074205957058951 52573927611308935588427)
              ·
                refine ⟨78860891416963403382641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52573927611308935588427 78860891416963403382641)
                ·
                  refine ⟨59145668562722552536981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78860891416963403382641 59145668562722552536981)
                  ·
                    refine ⟨2772453213877619650171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59145668562722552536981 2772453213877619650171)
                    ·
                      rfl

theorem cell23_16198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_16198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16198 prefixEnd_16198 := by exact prefixLift 16198
  have htrace : WordTrace (prefixWord ++ tailWord_16198) baseStart_16198 baseEnd_16198 := by
    simpa [prefixWord, tailWord_16198, baseEnd_16198] using wordTrace_append hprefix tailTrace_16198
  have hstable : (prefixWord ++ tailWord_16198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16198).length < 2 ^ (prefixWord ++ tailWord_16198).sum := by decide
  have hdescent : baseEnd_16198 < baseStart_16198 := by decide
  rcases family_descends (prefixWord ++ tailWord_16198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16205 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_16205 : Nat := 118140960795 + 16205 * 2 ^ 59
def prefixEnd_16205 : Nat := 4983230072969 + 3 ^ 40 * 16205 * 2
def baseEnd_16205 : Nat := 8320954006214331562981

theorem tailTrace_16205 : CollatzResearch.WordTrace tailWord_16205 prefixEnd_16205 8320954006214331562981 := by
  unfold tailWord_16205
  simp only [CollatzResearch.WordTrace]
  refine ⟨591044906299527438770069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 394029937533018292513379 591044906299527438770069)
  ·
    refine ⟨27705229982790348692347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 591044906299527438770069 27705229982790348692347)
    ·
      refine ⟨41557844974185523038521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27705229982790348692347 41557844974185523038521)
      ·
        refine ⟨31168383730639142278891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41557844974185523038521 31168383730639142278891)
        ·
          refine ⟨46752575595958713418337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31168383730639142278891 46752575595958713418337)
          ·
            refine ⟨35064431696969035063753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46752575595958713418337 35064431696969035063753)
            ·
              refine ⟨26298323772726776297815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35064431696969035063753 26298323772726776297815)
              ·
                refine ⟨39447485659090164446723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26298323772726776297815 39447485659090164446723)
                ·
                  refine ⟨59171228488635246670085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39447485659090164446723 59171228488635246670085)
                  ·
                    refine ⟨11094605341619108750641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59171228488635246670085 11094605341619108750641)
                    ·
                      refine ⟨8320954006214331562981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11094605341619108750641 8320954006214331562981)
                      ·
                        rfl

theorem cell23_16205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_16205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16205 prefixEnd_16205 := by exact prefixLift 16205
  have htrace : WordTrace (prefixWord ++ tailWord_16205) baseStart_16205 baseEnd_16205 := by
    simpa [prefixWord, tailWord_16205, baseEnd_16205] using wordTrace_append hprefix tailTrace_16205
  have hstable : (prefixWord ++ tailWord_16205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16205).length < 2 ^ (prefixWord ++ tailWord_16205).sum := by decide
  have hdescent : baseEnd_16205 < baseStart_16205 := by decide
  rcases family_descends (prefixWord ++ tailWord_16205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16224 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_16224 : Nat := 118140960795 + 16224 * 2 ^ 59
def prefixEnd_16224 : Nat := 4983230072969 + 3 ^ 40 * 16224 * 2
def baseEnd_16224 : Nat := 2776903379549919075131

theorem tailTrace_16224 : CollatzResearch.WordTrace tailWord_16224 prefixEnd_16224 2776903379549919075131 := by
  unfold tailWord_16224
  simp only [CollatzResearch.WordTrace]
  refine ⟨295868946615346841855863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 394491928820462455807817 295868946615346841855863)
  ·
    refine ⟨443803419923020262783795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295868946615346841855863 443803419923020262783795)
    ·
      refine ⟨665705129884530394175693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443803419923020262783795 665705129884530394175693)
      ·
        refine ⟨249639423706698897815885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665705129884530394175693 249639423706698897815885)
        ·
          refine ⟨93614783890012086680957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249639423706698897815885 93614783890012086680957)
          ·
            refine ⟨35105543958754532505359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93614783890012086680957 35105543958754532505359)
            ·
              refine ⟨52658315938131798758039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35105543958754532505359 52658315938131798758039)
              ·
                refine ⟨78987473907197698137059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52658315938131798758039 78987473907197698137059)
                ·
                  refine ⟨118481210860796547205589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78987473907197698137059 118481210860796547205589)
                  ·
                    refine ⟨2776903379549919075131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 118481210860796547205589 2776903379549919075131)
                    ·
                      rfl

theorem cell23_16224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_16224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16224 prefixEnd_16224 := by exact prefixLift 16224
  have htrace : WordTrace (prefixWord ++ tailWord_16224) baseStart_16224 baseEnd_16224 := by
    simpa [prefixWord, tailWord_16224, baseEnd_16224] using wordTrace_append hprefix tailTrace_16224
  have hstable : (prefixWord ++ tailWord_16224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16224).length < 2 ^ (prefixWord ++ tailWord_16224).sum := by decide
  have hdescent : baseEnd_16224 < baseStart_16224 := by decide
  rcases family_descends (prefixWord ++ tailWord_16224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16228 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 5]
def baseStart_16228 : Nat := 118140960795 + 16228 * 2 ^ 59
def prefixEnd_16228 : Nat := 4983230072969 + 3 ^ 40 * 16228 * 2
def baseEnd_16228 : Nat := 925862673474193508375

theorem tailTrace_16228 : CollatzResearch.WordTrace tailWord_16228 prefixEnd_16228 925862673474193508375 := by
  unfold tailWord_16228
  simp only [CollatzResearch.WordTrace]
  refine ⟨295941892608101183428669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 394589190144134911238225 295941892608101183428669)
  ·
    refine ⟨110978209728037943785751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295941892608101183428669 110978209728037943785751)
    ·
      refine ⟨166467314592056915678627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110978209728037943785751 166467314592056915678627)
      ·
        refine ⟨249700971888085373517941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166467314592056915678627 249700971888085373517941)
        ·
          refine ⟨23409466114508003767307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249700971888085373517941 23409466114508003767307)
          ·
            refine ⟨35114199171762005650961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23409466114508003767307 35114199171762005650961)
            ·
              refine ⟨26335649378821504238221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35114199171762005650961 26335649378821504238221)
              ·
                refine ⟨9875868517058064089333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26335649378821504238221 9875868517058064089333)
                ·
                  refine ⟨925862673474193508375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9875868517058064089333 925862673474193508375)
                  ·
                    rfl

theorem cell23_16228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_16228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16228 prefixEnd_16228 := by exact prefixLift 16228
  have htrace : WordTrace (prefixWord ++ tailWord_16228) baseStart_16228 baseEnd_16228 := by
    simpa [prefixWord, tailWord_16228, baseEnd_16228] using wordTrace_append hprefix tailTrace_16228
  have hstable : (prefixWord ++ tailWord_16228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16228).length < 2 ^ (prefixWord ++ tailWord_16228).sum := by decide
  have hdescent : baseEnd_16228 < baseStart_16228 := by decide
  rcases family_descends (prefixWord ++ tailWord_16228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16261 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_16261 : Nat := 118140960795 + 16261 * 2 ^ 59
def prefixEnd_16261 : Nat := 4983230072969 + 3 ^ 40 * 16261 * 2
def baseEnd_16261 : Nat := 8349708922866112462723

theorem tailTrace_16261 : CollatzResearch.WordTrace tailWord_16261 prefixEnd_16261 8349708922866112462723 := by
  unfold tailWord_16261
  simp only [CollatzResearch.WordTrace]
  refine ⟨593087394096649002808637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 395391596064432668539091 593087394096649002808637)
  ·
    refine ⟨222407772786243376053239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 593087394096649002808637 222407772786243376053239)
    ·
      refine ⟨333611659179365064079859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222407772786243376053239 333611659179365064079859)
      ·
        refine ⟨500417488769047596119789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333611659179365064079859 500417488769047596119789)
        ·
          refine ⟨187656558288392848544921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 500417488769047596119789 187656558288392848544921)
          ·
            refine ⟨140742418716294636408691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187656558288392848544921 140742418716294636408691)
            ·
              refine ⟨211113628074441954613037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140742418716294636408691 211113628074441954613037)
              ·
                refine ⟨79167610527915732979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211113628074441954613037 79167610527915732979889)
                ·
                  refine ⟨59375707895936799734917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79167610527915732979889 59375707895936799734917)
                  ·
                    refine ⟨11132945230488149950297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59375707895936799734917 11132945230488149950297)
                    ·
                      refine ⟨8349708922866112462723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11132945230488149950297 8349708922866112462723)
                      ·
                        rfl

theorem cell23_16261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_16261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16261 prefixEnd_16261 := by exact prefixLift 16261
  have htrace : WordTrace (prefixWord ++ tailWord_16261) baseStart_16261 baseEnd_16261 := by
    simpa [prefixWord, tailWord_16261, baseEnd_16261] using wordTrace_append hprefix tailTrace_16261
  have hstable : (prefixWord ++ tailWord_16261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16261).length < 2 ^ (prefixWord ++ tailWord_16261).sum := by decide
  have hdescent : baseEnd_16261 < baseStart_16261 := by decide
  rcases family_descends (prefixWord ++ tailWord_16261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16318 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_16318 : Nat := 118140960795 + 16318 * 2 ^ 59
def prefixEnd_16318 : Nat := 4983230072969 + 3 ^ 40 * 16318 * 2
def baseEnd_16318 : Nat := 930997480019154383329

theorem tailTrace_16318 : CollatzResearch.WordTrace tailWord_16318 prefixEnd_16318 930997480019154383329 := by
  unfold tailWord_16318
  simp only [CollatzResearch.WordTrace]
  refine ⟨74395794361268467204201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 396777569926765158422405 74395794361268467204201)
  ·
    refine ⟨55796845770951350403151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74395794361268467204201 55796845770951350403151)
    ·
      refine ⟨83695268656427025604727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55796845770951350403151 83695268656427025604727)
      ·
        refine ⟨125542902984640538407091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83695268656427025604727 125542902984640538407091)
        ·
          refine ⟨188314354476960807610637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125542902984640538407091 188314354476960807610637)
          ·
            refine ⟨70617882928860302853989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188314354476960807610637 70617882928860302853989)
            ·
              refine ⟨13240853049161306785123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70617882928860302853989 13240853049161306785123)
              ·
                refine ⟨19861279573741960177685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240853049161306785123 19861279573741960177685)
                ·
                  refine ⟨930997480019154383329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19861279573741960177685 930997480019154383329)
                  ·
                    rfl

theorem cell23_16318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_16318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16318 prefixEnd_16318 := by exact prefixLift 16318
  have htrace : WordTrace (prefixWord ++ tailWord_16318) baseStart_16318 baseEnd_16318 := by
    simpa [prefixWord, tailWord_16318, baseEnd_16318] using wordTrace_append hprefix tailTrace_16318
  have hstable : (prefixWord ++ tailWord_16318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16318).length < 2 ^ (prefixWord ++ tailWord_16318).sum := by decide
  have hdescent : baseEnd_16318 < baseStart_16318 := by decide
  rcases family_descends (prefixWord ++ tailWord_16318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16364 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_16364 : Nat := 118140960795 + 16364 * 2 ^ 59
def prefixEnd_16364 : Nat := 4983230072969 + 3 ^ 40 * 16364 * 2
def baseEnd_16364 : Nat := 8402597430279209474749

theorem tailTrace_16364 : CollatzResearch.WordTrace tailWord_16364 prefixEnd_16364 8402597430279209474749 := by
  unfold tailWord_16364
  simp only [CollatzResearch.WordTrace]
  refine ⟨298422056361748796904073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 397896075148998395872097 298422056361748796904073)
  ·
    refine ⟨223816542271311597678055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298422056361748796904073 223816542271311597678055)
    ·
      refine ⟨335724813406967396517083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223816542271311597678055 335724813406967396517083)
      ·
        refine ⟨503587220110451094775625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335724813406967396517083 503587220110451094775625)
        ·
          refine ⟨377690415082838321081719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503587220110451094775625 377690415082838321081719)
          ·
            refine ⟨566535622624257481622579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377690415082838321081719 566535622624257481622579)
            ·
              refine ⟨849803433936386222433869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566535622624257481622579 849803433936386222433869)
              ·
                refine ⟨318676287726144833412701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 849803433936386222433869 318676287726144833412701)
                ·
                  refine ⟨119503607897304312529763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318676287726144833412701 119503607897304312529763)
                  ·
                    refine ⟨179255411845956468794645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119503607897304312529763 179255411845956468794645)
                    ·
                      refine ⟨8402597430279209474749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 179255411845956468794645 8402597430279209474749)
                      ·
                        rfl

theorem cell23_16364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_16364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16364 prefixEnd_16364 := by exact prefixLift 16364
  have htrace : WordTrace (prefixWord ++ tailWord_16364) baseStart_16364 baseEnd_16364 := by
    simpa [prefixWord, tailWord_16364, baseEnd_16364] using wordTrace_append hprefix tailTrace_16364
  have hstable : (prefixWord ++ tailWord_16364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16364).length < 2 ^ (prefixWord ++ tailWord_16364).sum := by decide
  have hdescent : baseEnd_16364 < baseStart_16364 := by decide
  rcases family_descends (prefixWord ++ tailWord_16364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16381 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_16381 : Nat := 118140960795 + 16381 * 2 ^ 59
def prefixEnd_16381 : Nat := 4983230072969 + 3 ^ 40 * 16381 * 2
def baseEnd_16381 : Nat := 8411326601405642962171

theorem tailTrace_16381 : CollatzResearch.WordTrace tailWord_16381 prefixEnd_16381 8411326601405642962171 := by
  unfold tailWord_16381
  simp only [CollatzResearch.WordTrace]
  refine ⟨597464153661909497176997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398309435774606331451331 597464153661909497176997)
  ·
    refine ⟨112024528811608030720687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 597464153661909497176997 112024528811608030720687)
    ·
      refine ⟨168036793217412046081031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112024528811608030720687 168036793217412046081031)
      ·
        refine ⟨252055189826118069121547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168036793217412046081031 252055189826118069121547)
        ·
          refine ⟨378082784739177103682321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252055189826118069121547 378082784739177103682321)
          ·
            refine ⟨283562088554382827761741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378082784739177103682321 283562088554382827761741)
            ·
              refine ⟨106335783207893560410653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283562088554382827761741 106335783207893560410653)
              ·
                refine ⟨39875918702960085153995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106335783207893560410653 39875918702960085153995)
                ·
                  refine ⟨59813878054440127730993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39875918702960085153995 59813878054440127730993)
                  ·
                    refine ⟨44860408540830095798245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59813878054440127730993 44860408540830095798245)
                    ·
                      refine ⟨8411326601405642962171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 44860408540830095798245 8411326601405642962171)
                      ·
                        rfl

theorem cell23_16381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_16381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16381 prefixEnd_16381 := by exact prefixLift 16381
  have htrace : WordTrace (prefixWord ++ tailWord_16381) baseStart_16381 baseEnd_16381 := by
    simpa [prefixWord, tailWord_16381, baseEnd_16381] using wordTrace_append hprefix tailTrace_16381
  have hstable : (prefixWord ++ tailWord_16381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16381).length < 2 ^ (prefixWord ++ tailWord_16381).sum := by decide
  have hdescent : baseEnd_16381 < baseStart_16381 := by decide
  rcases family_descends (prefixWord ++ tailWord_16381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16385 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_16385 : Nat := 118140960795 + 16385 * 2 ^ 59
def prefixEnd_16385 : Nat := 4983230072969 + 3 ^ 40 * 16385 * 2
def baseEnd_16385 : Nat := 8413380524023627312153

theorem tailTrace_16385 : CollatzResearch.WordTrace tailWord_16385 prefixEnd_16385 8413380524023627312153 := by
  unfold tailWord_16385
  simp only [CollatzResearch.WordTrace]
  refine ⟨597610045647418180322609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398406697098278786881739 597610045647418180322609)
  ·
    refine ⟨448207534235563635241957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597610045647418180322609 448207534235563635241957)
    ·
      refine ⟨84038912669168181607867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448207534235563635241957 84038912669168181607867)
      ·
        refine ⟨126058369003752272411801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84038912669168181607867 126058369003752272411801)
        ·
          refine ⟨94543776752814204308851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126058369003752272411801 94543776752814204308851)
          ·
            refine ⟨141815665129221306463277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94543776752814204308851 141815665129221306463277)
            ·
              refine ⟨53180874423457989923729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141815665129221306463277 53180874423457989923729)
              ·
                refine ⟨39885655817593492442797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53180874423457989923729 39885655817593492442797)
                ·
                  refine ⟨14957120931597559666049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39885655817593492442797 14957120931597559666049)
                  ·
                    refine ⟨11217840698698169749537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14957120931597559666049 11217840698698169749537)
                    ·
                      refine ⟨8413380524023627312153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11217840698698169749537 8413380524023627312153)
                      ·
                        rfl

theorem cell23_16385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_16385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16385 prefixEnd_16385 := by exact prefixLift 16385
  have htrace : WordTrace (prefixWord ++ tailWord_16385) baseStart_16385 baseEnd_16385 := by
    simpa [prefixWord, tailWord_16385, baseEnd_16385] using wordTrace_append hprefix tailTrace_16385
  have hstable : (prefixWord ++ tailWord_16385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16385).length < 2 ^ (prefixWord ++ tailWord_16385).sum := by decide
  have hdescent : baseEnd_16385 < baseStart_16385 := by decide
  rcases family_descends (prefixWord ++ tailWord_16385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16405 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_16405 : Nat := 118140960795 + 16405 * 2 ^ 59
def prefixEnd_16405 : Nat := 4983230072969 + 3 ^ 40 * 16405 * 2
def baseEnd_16405 : Nat := 8423650137113549062061

theorem tailTrace_16405 : CollatzResearch.WordTrace tailWord_16405 prefixEnd_16405 8423650137113549062061 := by
  unfold tailWord_16405
  simp only [CollatzResearch.WordTrace]
  refine ⟨598339505574961596050669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398893003716641064033779 598339505574961596050669)
  ·
    refine ⟨224377314590610598519001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 598339505574961596050669 224377314590610598519001)
    ·
      refine ⟨168282985942957948889251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224377314590610598519001 168282985942957948889251)
      ·
        refine ⟨252424478914436923333877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168282985942957948889251 252424478914436923333877)
        ·
          refine ⟨23664794898228461562551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252424478914436923333877 23664794898228461562551)
          ·
            refine ⟨35497192347342692343827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23664794898228461562551 35497192347342692343827)
            ·
              refine ⟨53245788521014038515741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35497192347342692343827 53245788521014038515741)
              ·
                refine ⟨19967170695380264443403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53245788521014038515741 19967170695380264443403)
                ·
                  refine ⟨29950756043070396665105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967170695380264443403 29950756043070396665105)
                  ·
                    refine ⟨22463067032302797498829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29950756043070396665105 22463067032302797498829)
                    ·
                      refine ⟨8423650137113549062061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22463067032302797498829 8423650137113549062061)
                      ·
                        rfl

theorem cell23_16405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_16405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16405 prefixEnd_16405 := by exact prefixLift 16405
  have htrace : WordTrace (prefixWord ++ tailWord_16405) baseStart_16405 baseEnd_16405 := by
    simpa [prefixWord, tailWord_16405, baseEnd_16405] using wordTrace_append hprefix tailTrace_16405
  have hstable : (prefixWord ++ tailWord_16405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16405).length < 2 ^ (prefixWord ++ tailWord_16405).sum := by decide
  have hdescent : baseEnd_16405 < baseStart_16405 := by decide
  rcases family_descends (prefixWord ++ tailWord_16405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_16428 : Nat := 118140960795 + 16428 * 2 ^ 59
def prefixEnd_16428 : Nat := 4983230072969 + 3 ^ 40 * 16428 * 2
def baseEnd_16428 : Nat := 8435460192166959074455

theorem tailTrace_16428 : CollatzResearch.WordTrace tailWord_16428 prefixEnd_16428 8435460192166959074455 := by
  unfold tailWord_16428
  simp only [CollatzResearch.WordTrace]
  refine ⟨299589192245818262068969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 399452256327757682758625 299589192245818262068969)
  ·
    refine ⟨224691894184363696551727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299589192245818262068969 224691894184363696551727)
    ·
      refine ⟨337037841276545544827591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224691894184363696551727 337037841276545544827591)
      ·
        refine ⟨505556761914818317241387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337037841276545544827591 505556761914818317241387)
        ·
          refine ⟨758335142872227475862081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505556761914818317241387 758335142872227475862081)
          ·
            refine ⟨568751357154170606896561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 758335142872227475862081 568751357154170606896561)
            ·
              refine ⟨426563517865627955172421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568751357154170606896561 426563517865627955172421)
              ·
                refine ⟨79980659599805241594829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 426563517865627955172421 79980659599805241594829)
                ·
                  refine ⟨29992747349926965598061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79980659599805241594829 29992747349926965598061)
                  ·
                    refine ⟨11247280256222612099273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29992747349926965598061 11247280256222612099273)
                    ·
                      refine ⟨8435460192166959074455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11247280256222612099273 8435460192166959074455)
                      ·
                        rfl

theorem cell23_16428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_16428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16428 prefixEnd_16428 := by exact prefixLift 16428
  have htrace : WordTrace (prefixWord ++ tailWord_16428) baseStart_16428 baseEnd_16428 := by
    simpa [prefixWord, tailWord_16428, baseEnd_16428] using wordTrace_append hprefix tailTrace_16428
  have hstable : (prefixWord ++ tailWord_16428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16428).length < 2 ^ (prefixWord ++ tailWord_16428).sum := by decide
  have hdescent : baseEnd_16428 < baseStart_16428 := by decide
  rcases family_descends (prefixWord ++ tailWord_16428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_16458 : Nat := 118140960795 + 16458 * 2 ^ 59
def prefixEnd_16458 : Nat := 4983230072969 + 3 ^ 40 * 16458 * 2
def baseEnd_16458 : Nat := 8450864611801841699317

theorem tailTrace_16458 : CollatzResearch.WordTrace tailWord_16458 prefixEnd_16458 8450864611801841699317 := by
  unfold tailWord_16458
  simp only [CollatzResearch.WordTrace]
  refine ⟨150068143595737911932507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 400181716255301098486685 150068143595737911932507)
  ·
    refine ⟨225102215393606867898761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150068143595737911932507 225102215393606867898761)
    ·
      refine ⟨168826661545205150924071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 225102215393606867898761 168826661545205150924071)
      ·
        refine ⟨253239992317807726386107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168826661545205150924071 253239992317807726386107)
        ·
          refine ⟨379859988476711589579161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253239992317807726386107 379859988476711589579161)
          ·
            refine ⟨284894991357533692184371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379859988476711589579161 284894991357533692184371)
            ·
              refine ⟨427342487036300538276557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284894991357533692184371 427342487036300538276557)
              ·
                refine ⟨160253432638612701853709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427342487036300538276557 160253432638612701853709)
                ·
                  refine ⟨60095037239479763195141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 160253432638612701853709 60095037239479763195141)
                  ·
                    refine ⟨11267819482402455599089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60095037239479763195141 11267819482402455599089)
                    ·
                      refine ⟨8450864611801841699317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11267819482402455599089 8450864611801841699317)
                      ·
                        rfl

theorem cell23_16458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_16458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16458 prefixEnd_16458 := by exact prefixLift 16458
  have htrace : WordTrace (prefixWord ++ tailWord_16458) baseStart_16458 baseEnd_16458 := by
    simpa [prefixWord, tailWord_16458, baseEnd_16458] using wordTrace_append hprefix tailTrace_16458
  have hstable : (prefixWord ++ tailWord_16458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16458).length < 2 ^ (prefixWord ++ tailWord_16458).sum := by decide
  have hdescent : baseEnd_16458 < baseStart_16458 := by decide
  rcases family_descends (prefixWord ++ tailWord_16458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16471 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_16471 : Nat := 118140960795 + 16471 * 2 ^ 59
def prefixEnd_16471 : Nat := 4983230072969 + 3 ^ 40 * 16471 * 2
def baseEnd_16471 : Nat := 8457539860310290836757

theorem tailTrace_16471 : CollatzResearch.WordTrace tailWord_16471 prefixEnd_16471 8457539860310290836757 := by
  unfold tailWord_16471
  simp only [CollatzResearch.WordTrace]
  refine ⟨600746723335854867953267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 400497815557236578635511 600746723335854867953267)
  ·
    refine ⟨901120085003782301929901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 600746723335854867953267 901120085003782301929901)
    ·
      refine ⟨337920031876418363223713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 901120085003782301929901 337920031876418363223713)
      ·
        refine ⟨253440023907313772417785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337920031876418363223713 253440023907313772417785)
        ·
          refine ⟨190080017930485329313339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253440023907313772417785 190080017930485329313339)
          ·
            refine ⟨285120026895727993970009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190080017930485329313339 285120026895727993970009)
            ·
              refine ⟨213840020171795995477507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285120026895727993970009 213840020171795995477507)
              ·
                refine ⟨320760030257693993216261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213840020171795995477507 320760030257693993216261)
                ·
                  refine ⟨60142505673317623728049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 320760030257693993216261 60142505673317623728049)
                  ·
                    refine ⟨45106879254988217796037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60142505673317623728049 45106879254988217796037)
                    ·
                      refine ⟨8457539860310290836757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 45106879254988217796037 8457539860310290836757)
                      ·
                        rfl

theorem cell23_16471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_16471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16471 prefixEnd_16471 := by exact prefixLift 16471
  have htrace : WordTrace (prefixWord ++ tailWord_16471) baseStart_16471 baseEnd_16471 := by
    simpa [prefixWord, tailWord_16471, baseEnd_16471] using wordTrace_append hprefix tailTrace_16471
  have hstable : (prefixWord ++ tailWord_16471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16471).length < 2 ^ (prefixWord ++ tailWord_16471).sum := by decide
  have hdescent : baseEnd_16471 < baseStart_16471 := by decide
  rcases family_descends (prefixWord ++ tailWord_16471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16492 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_16492 : Nat := 118140960795 + 16492 * 2 ^ 59
def prefixEnd_16492 : Nat := 4983230072969 + 3 ^ 40 * 16492 * 2
def baseEnd_16492 : Nat := 8468322954054708674161

theorem tailTrace_16492 : CollatzResearch.WordTrace tailWord_16492 prefixEnd_16492 8468322954054708674161 := by
  unfold tailWord_16492
  simp only [CollatzResearch.WordTrace]
  refine ⟨300756328129887727233865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 401008437506516969645153 300756328129887727233865)
  ·
    refine ⟨225567246097415795425399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 300756328129887727233865 225567246097415795425399)
    ·
      refine ⟨338350869146123693138099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225567246097415795425399 338350869146123693138099)
      ·
        refine ⟨507526303719185539707149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338350869146123693138099 507526303719185539707149)
        ·
          refine ⟨190322363894694577390181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507526303719185539707149 190322363894694577390181)
          ·
            refine ⟨35685443230255233260659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190322363894694577390181 35685443230255233260659)
            ·
              refine ⟨53528164845382849890989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35685443230255233260659 53528164845382849890989)
              ·
                refine ⟨20073061817018568709121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53528164845382849890989 20073061817018568709121)
                ·
                  refine ⟨15054796362763926531841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20073061817018568709121 15054796362763926531841)
                  ·
                    refine ⟨11291097272072944898881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15054796362763926531841 11291097272072944898881)
                    ·
                      refine ⟨8468322954054708674161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11291097272072944898881 8468322954054708674161)
                      ·
                        rfl

theorem cell23_16492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_16492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16492 prefixEnd_16492 := by exact prefixLift 16492
  have htrace : WordTrace (prefixWord ++ tailWord_16492) baseStart_16492 baseEnd_16492 := by
    simpa [prefixWord, tailWord_16492, baseEnd_16492] using wordTrace_append hprefix tailTrace_16492
  have hstable : (prefixWord ++ tailWord_16492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16492).length < 2 ^ (prefixWord ++ tailWord_16492).sum := by decide
  have hdescent : baseEnd_16492 < baseStart_16492 := by decide
  rcases family_descends (prefixWord ++ tailWord_16492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16521 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_16521 : Nat := 118140960795 + 16521 * 2 ^ 59
def prefixEnd_16521 : Nat := 4983230072969 + 3 ^ 40 * 16521 * 2
def baseEnd_16521 : Nat := 8483213893035095211527

theorem tailTrace_16521 : CollatzResearch.WordTrace tailWord_16521 prefixEnd_16521 8483213893035095211527 := by
  unfold tailWord_16521
  simp only [CollatzResearch.WordTrace]
  refine ⟨602570373154713407273417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 401713582103142271515611 602570373154713407273417)
  ·
    refine ⟨451927779866035055455063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 602570373154713407273417 451927779866035055455063)
    ·
      refine ⟨677891669799052583182595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451927779866035055455063 677891669799052583182595)
      ·
        refine ⟨1016837504698578874773893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 677891669799052583182595 1016837504698578874773893)
        ·
          refine ⟨190657032130983539020105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1016837504698578874773893 190657032130983539020105)
          ·
            refine ⟨142992774098237654265079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190657032130983539020105 142992774098237654265079)
            ·
              refine ⟨214489161147356481397619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142992774098237654265079 214489161147356481397619)
              ·
                refine ⟨321733741721034722096429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214489161147356481397619 321733741721034722096429)
                ·
                  refine ⟨120650153145388020786161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321733741721034722096429 120650153145388020786161)
                  ·
                    refine ⟨90487614859041015589621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 120650153145388020786161 90487614859041015589621)
                    ·
                      refine ⟨8483213893035095211527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 90487614859041015589621 8483213893035095211527)
                      ·
                        rfl

theorem cell23_16521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_16521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16521 prefixEnd_16521 := by exact prefixLift 16521
  have htrace : WordTrace (prefixWord ++ tailWord_16521) baseStart_16521 baseEnd_16521 := by
    simpa [prefixWord, tailWord_16521, baseEnd_16521] using wordTrace_append hprefix tailTrace_16521
  have hstable : (prefixWord ++ tailWord_16521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16521).length < 2 ^ (prefixWord ++ tailWord_16521).sum := by decide
  have hdescent : baseEnd_16521 < baseStart_16521 := by decide
  rcases family_descends (prefixWord ++ tailWord_16521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16531 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_16531 : Nat := 118140960795 + 16531 * 2 ^ 59
def prefixEnd_16531 : Nat := 4983230072969 + 3 ^ 40 * 16531 * 2
def baseEnd_16531 : Nat := 8488348699580056086481

theorem tailTrace_16531 : CollatzResearch.WordTrace tailWord_16531 prefixEnd_16531 8488348699580056086481 := by
  unfold tailWord_16531
  simp only [CollatzResearch.WordTrace]
  refine ⟨602935103118485115137447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 401956735412323410091631 602935103118485115137447)
  ·
    refine ⟨904402654677727672706171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 602935103118485115137447 904402654677727672706171)
    ·
      refine ⟨1356603982016591509059257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 904402654677727672706171 1356603982016591509059257)
      ·
        refine ⟨1017452986512443631794443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356603982016591509059257 1017452986512443631794443)
        ·
          refine ⟨1526179479768665447691665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017452986512443631794443 1526179479768665447691665)
          ·
            refine ⟨1144634609826499085768749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1526179479768665447691665 1144634609826499085768749)
            ·
              refine ⟨429237978684937157163281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1144634609826499085768749 429237978684937157163281)
              ·
                refine ⟨321928484013702867872461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429237978684937157163281 321928484013702867872461)
                ·
                  refine ⟨120723181505138575452173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321928484013702867872461 120723181505138575452173)
                  ·
                    refine ⟨45271193064426965794565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 120723181505138575452173 45271193064426965794565)
                    ·
                      refine ⟨8488348699580056086481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 45271193064426965794565 8488348699580056086481)
                      ·
                        rfl

theorem cell23_16531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_16531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16531 prefixEnd_16531 := by exact prefixLift 16531
  have htrace : WordTrace (prefixWord ++ tailWord_16531) baseStart_16531 baseEnd_16531 := by
    simpa [prefixWord, tailWord_16531, baseEnd_16531] using wordTrace_append hprefix tailTrace_16531
  have hstable : (prefixWord ++ tailWord_16531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16531).length < 2 ^ (prefixWord ++ tailWord_16531).sum := by decide
  have hdescent : baseEnd_16531 < baseStart_16531 := by decide
  rcases family_descends (prefixWord ++ tailWord_16531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16542 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_16542 : Nat := 118140960795 + 16542 * 2 ^ 59
def prefixEnd_16542 : Nat := 4983230072969 + 3 ^ 40 * 16542 * 2
def baseEnd_16542 : Nat := 8493996986779513048931

theorem tailTrace_16542 : CollatzResearch.WordTrace tailWord_16542 prefixEnd_16542 8493996986779513048931 := by
  unfold tailWord_16542
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417038259829249223485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 402224204052422662525253 75417038259829249223485)
  ·
    refine ⟨28281389347435968458807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75417038259829249223485 28281389347435968458807)
    ·
      refine ⟨42422084021153952688211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28281389347435968458807 42422084021153952688211)
      ·
        refine ⟨63633126031730929032317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42422084021153952688211 63633126031730929032317)
        ·
          refine ⟨23862422261899098387119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63633126031730929032317 23862422261899098387119)
          ·
            refine ⟨35793633392848647580679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862422261899098387119 35793633392848647580679)
            ·
              refine ⟨53690450089272971371019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35793633392848647580679 53690450089272971371019)
              ·
                refine ⟨80535675133909457056529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53690450089272971371019 80535675133909457056529)
                ·
                  refine ⟨60401756350432092792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80535675133909457056529 60401756350432092792397)
                  ·
                    refine ⟨22650658631412034797149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60401756350432092792397 22650658631412034797149)
                    ·
                      refine ⟨8493996986779513048931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22650658631412034797149 8493996986779513048931)
                      ·
                        rfl

theorem cell23_16542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_16542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16542 prefixEnd_16542 := by exact prefixLift 16542
  have htrace : WordTrace (prefixWord ++ tailWord_16542) baseStart_16542 baseEnd_16542 := by
    simpa [prefixWord, tailWord_16542, baseEnd_16542] using wordTrace_append hprefix tailTrace_16542
  have hstable : (prefixWord ++ tailWord_16542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16542).length < 2 ^ (prefixWord ++ tailWord_16542).sum := by decide
  have hdescent : baseEnd_16542 < baseStart_16542 := by decide
  rcases family_descends (prefixWord ++ tailWord_16542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16568 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_16568 : Nat := 118140960795 + 16568 * 2 ^ 59
def prefixEnd_16568 : Nat := 4983230072969 + 3 ^ 40 * 16568 * 2
def baseEnd_16568 : Nat := 8507347483796411323811

theorem tailTrace_16568 : CollatzResearch.WordTrace tailWord_16568 prefixEnd_16568 8507347483796411323811 := by
  unfold tailWord_16568
  simp only [CollatzResearch.WordTrace]
  refine ⟨302142301992220217117179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 402856402656293622822905 302142301992220217117179)
  ·
    refine ⟨453213452988330325675769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302142301992220217117179 453213452988330325675769)
    ·
      refine ⟨339910089741247744256827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453213452988330325675769 339910089741247744256827)
      ·
        refine ⟨509865134611871616385241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339910089741247744256827 509865134611871616385241)
        ·
          refine ⟨382398850958903712288931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 509865134611871616385241 382398850958903712288931)
          ·
            refine ⟨573598276438355568433397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382398850958903712288931 573598276438355568433397)
            ·
              refine ⟨53774838416095834540631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 573598276438355568433397 53774838416095834540631)
              ·
                refine ⟨80662257624143751810947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53774838416095834540631 80662257624143751810947)
                ·
                  refine ⟨120993386436215627716421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80662257624143751810947 120993386436215627716421)
                  ·
                    refine ⟨22686259956790430196829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 120993386436215627716421 22686259956790430196829)
                    ·
                      refine ⟨8507347483796411323811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22686259956790430196829 8507347483796411323811)
                      ·
                        rfl

theorem cell23_16568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_16568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16568 prefixEnd_16568 := by exact prefixLift 16568
  have htrace : WordTrace (prefixWord ++ tailWord_16568) baseStart_16568 baseEnd_16568 := by
    simpa [prefixWord, tailWord_16568, baseEnd_16568] using wordTrace_append hprefix tailTrace_16568
  have hstable : (prefixWord ++ tailWord_16568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16568).length < 2 ^ (prefixWord ++ tailWord_16568).sum := by decide
  have hdescent : baseEnd_16568 < baseStart_16568 := by decide
  rcases family_descends (prefixWord ++ tailWord_16568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16571 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 8]
def baseStart_16571 : Nat := 118140960795 + 16571 * 2 ^ 59
def prefixEnd_16571 : Nat := 4983230072969 + 3 ^ 40 * 16571 * 2
def baseEnd_16571 : Nat := 945431991751099954033

theorem tailTrace_16571 : CollatzResearch.WordTrace tailWord_16571 prefixEnd_16571 945431991751099954033 := by
  unfold tailWord_16571
  simp only [CollatzResearch.WordTrace]
  refine ⟨604394022973571946593567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 402929348649047964395711 604394022973571946593567)
  ·
    refine ⟨906591034460357919890351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 604394022973571946593567 906591034460357919890351)
    ·
      refine ⟨1359886551690536879835527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906591034460357919890351 1359886551690536879835527)
      ·
        refine ⟨2039829827535805319753291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1359886551690536879835527 2039829827535805319753291)
        ·
          refine ⟨3059744741303707979629937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039829827535805319753291 3059744741303707979629937)
          ·
            refine ⟨2294808555977780984722453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3059744741303707979629937 2294808555977780984722453)
            ·
              refine ⟨107569151061458483658865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2294808555977780984722453 107569151061458483658865)
              ·
                refine ⟨80676863296093862744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107569151061458483658865 80676863296093862744149)
                ·
                  refine ⟨945431991751099954033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 80676863296093862744149 945431991751099954033)
                  ·
                    rfl

theorem cell23_16571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_16571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16571 prefixEnd_16571 := by exact prefixLift 16571
  have htrace : WordTrace (prefixWord ++ tailWord_16571) baseStart_16571 baseEnd_16571 := by
    simpa [prefixWord, tailWord_16571, baseEnd_16571] using wordTrace_append hprefix tailTrace_16571
  have hstable : (prefixWord ++ tailWord_16571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16571).length < 2 ^ (prefixWord ++ tailWord_16571).sum := by decide
  have hdescent : baseEnd_16571 < baseStart_16571 := by decide
  rcases family_descends (prefixWord ++ tailWord_16571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16591 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_16591 : Nat := 118140960795 + 16591 * 2 ^ 59
def prefixEnd_16591 : Nat := 4983230072969 + 3 ^ 40 * 16591 * 2
def baseEnd_16591 : Nat := 8519157538849821336205

theorem tailTrace_16591 : CollatzResearch.WordTrace tailWord_16591 prefixEnd_16591 8519157538849821336205 := by
  unfold tailWord_16591
  simp only [CollatzResearch.WordTrace]
  refine ⟨605123482901115362321627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 403415655267410241547751 605123482901115362321627)
  ·
    refine ⟨907685224351673043482441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605123482901115362321627 907685224351673043482441)
    ·
      refine ⟨680763918263754782611831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907685224351673043482441 680763918263754782611831)
      ·
        refine ⟨1021145877395632173917747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680763918263754782611831 1021145877395632173917747)
        ·
          refine ⟨1531718816093448260876621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021145877395632173917747 1531718816093448260876621)
          ·
            refine ⟨574394556035043097828733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1531718816093448260876621 574394556035043097828733)
            ·
              refine ⟨215397958513141161685775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574394556035043097828733 215397958513141161685775)
              ·
                refine ⟨323096937769711742528663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215397958513141161685775 323096937769711742528663)
                ·
                  refine ⟨484645406654567613792995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 323096937769711742528663 484645406654567613792995)
                  ·
                    refine ⟨726968109981851420689493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 484645406654567613792995 726968109981851420689493)
                    ·
                      refine ⟨8519157538849821336205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 726968109981851420689493 8519157538849821336205)
                      ·
                        rfl

theorem cell23_16591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_16591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16591 prefixEnd_16591 := by exact prefixLift 16591
  have htrace : WordTrace (prefixWord ++ tailWord_16591) baseStart_16591 baseEnd_16591 := by
    simpa [prefixWord, tailWord_16591, baseEnd_16591] using wordTrace_append hprefix tailTrace_16591
  have hstable : (prefixWord ++ tailWord_16591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16591).length < 2 ^ (prefixWord ++ tailWord_16591).sum := by decide
  have hdescent : baseEnd_16591 < baseStart_16591 := by decide
  rcases family_descends (prefixWord ++ tailWord_16591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16625 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_16625 : Nat := 118140960795 + 16625 * 2 ^ 59
def prefixEnd_16625 : Nat := 4983230072969 + 3 ^ 40 * 16625 * 2
def baseEnd_16625 : Nat := 8536615881102688311049

theorem tailTrace_16625 : CollatzResearch.WordTrace tailWord_16625 prefixEnd_16625 8536615881102688311049 := by
  unfold tailWord_16625
  simp only [CollatzResearch.WordTrace]
  refine ⟨606363564777939169059329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 404242376518626112706219 606363564777939169059329)
  ·
    refine ⟨454772673583454376794497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 606363564777939169059329 454772673583454376794497)
    ·
      refine ⟨341079505187590782595873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454772673583454376794497 341079505187590782595873)
      ·
        refine ⟨255809628890693086946905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341079505187590782595873 255809628890693086946905)
        ·
          refine ⟨191857221668019815210179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255809628890693086946905 191857221668019815210179)
          ·
            refine ⟨287785832502029722815269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191857221668019815210179 287785832502029722815269)
            ·
              refine ⟨53959843594130573027863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287785832502029722815269 53959843594130573027863)
              ·
                refine ⟨80939765391195859541795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53959843594130573027863 80939765391195859541795)
                ·
                  refine ⟨121409648086793789312693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80939765391195859541795 121409648086793789312693)
                  ·
                    refine ⟨11382154508136917748065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121409648086793789312693 11382154508136917748065)
                    ·
                      refine ⟨8536615881102688311049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11382154508136917748065 8536615881102688311049)
                      ·
                        rfl

theorem cell23_16625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_16625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16625 prefixEnd_16625 := by exact prefixLift 16625
  have htrace : WordTrace (prefixWord ++ tailWord_16625) baseStart_16625 baseEnd_16625 := by
    simpa [prefixWord, tailWord_16625, baseEnd_16625] using wordTrace_append hprefix tailTrace_16625
  have hstable : (prefixWord ++ tailWord_16625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16625).length < 2 ^ (prefixWord ++ tailWord_16625).sum := by decide
  have hdescent : baseEnd_16625 < baseStart_16625 := by decide
  rcases family_descends (prefixWord ++ tailWord_16625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16669 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_16669 : Nat := 118140960795 + 16669 * 2 ^ 59
def prefixEnd_16669 : Nat := 4983230072969 + 3 ^ 40 * 16669 * 2
def baseEnd_16669 : Nat := 2853069676633505386949

theorem tailTrace_16669 : CollatzResearch.WordTrace tailWord_16669 prefixEnd_16669 2853069676633505386949 := by
  unfold tailWord_16669
  simp only [CollatzResearch.WordTrace]
  refine ⟨607968376618534683661061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 405312251079023122440707 607968376618534683661061)
  ·
    refine ⟨113994070615975253186449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 607968376618534683661061 113994070615975253186449)
    ·
      refine ⟨85495552961981439889837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113994070615975253186449 85495552961981439889837)
      ·
        refine ⟨32060832360743039958689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85495552961981439889837 32060832360743039958689)
        ·
          refine ⟨24045624270557279969017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32060832360743039958689 24045624270557279969017)
          ·
            refine ⟨18034218202917959976763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24045624270557279969017 18034218202917959976763)
            ·
              refine ⟨27051327304376939965145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18034218202917959976763 27051327304376939965145)
              ·
                refine ⟨20288495478282704973859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27051327304376939965145 20288495478282704973859)
                ·
                  refine ⟨30432743217424057460789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20288495478282704973859 30432743217424057460789)
                  ·
                    refine ⟨2853069676633505386949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30432743217424057460789 2853069676633505386949)
                    ·
                      rfl

theorem cell23_16669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_16669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16669 prefixEnd_16669 := by exact prefixLift 16669
  have htrace : WordTrace (prefixWord ++ tailWord_16669) baseStart_16669 baseEnd_16669 := by
    simpa [prefixWord, tailWord_16669, baseEnd_16669] using wordTrace_append hprefix tailTrace_16669
  have hstable : (prefixWord ++ tailWord_16669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16669).length < 2 ^ (prefixWord ++ tailWord_16669).sum := by decide
  have hdescent : baseEnd_16669 < baseStart_16669 := by decide
  rcases family_descends (prefixWord ++ tailWord_16669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16672 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_16672 : Nat := 118140960795 + 16672 * 2 ^ 59
def prefixEnd_16672 : Nat := 4983230072969 + 3 ^ 40 * 16672 * 2
def baseEnd_16672 : Nat := 8560749471864004423333

theorem tailTrace_16672 : CollatzResearch.WordTrace tailWord_16672 prefixEnd_16672 8560749471864004423333 := by
  unfold tailWord_16672
  simp only [CollatzResearch.WordTrace]
  refine ⟨304038897803833098010135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 405385197071777464013513 304038897803833098010135)
  ·
    refine ⟨456058346705749647015203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304038897803833098010135 456058346705749647015203)
    ·
      refine ⟨684087520058624470522805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 456058346705749647015203 684087520058624470522805)
      ·
        refine ⟨64133205005496044111513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 684087520058624470522805 64133205005496044111513)
        ·
          refine ⟨48099903754122033083635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64133205005496044111513 48099903754122033083635)
          ·
            refine ⟨72149855631183049625453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48099903754122033083635 72149855631183049625453)
            ·
              refine ⟨27056195861693643609545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72149855631183049625453 27056195861693643609545)
              ·
                refine ⟨20292146896270232707159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27056195861693643609545 20292146896270232707159)
                ·
                  refine ⟨30438220344405349060739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20292146896270232707159 30438220344405349060739)
                  ·
                    refine ⟨45657330516608023591109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30438220344405349060739 45657330516608023591109)
                    ·
                      refine ⟨8560749471864004423333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 45657330516608023591109 8560749471864004423333)
                      ·
                        rfl

theorem cell23_16672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_16672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16672 prefixEnd_16672 := by exact prefixLift 16672
  have htrace : WordTrace (prefixWord ++ tailWord_16672) baseStart_16672 baseEnd_16672 := by
    simpa [prefixWord, tailWord_16672, baseEnd_16672] using wordTrace_append hprefix tailTrace_16672
  have hstable : (prefixWord ++ tailWord_16672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16672).length < 2 ^ (prefixWord ++ tailWord_16672).sum := by decide
  have hdescent : baseEnd_16672 < baseStart_16672 := by decide
  rcases family_descends (prefixWord ++ tailWord_16672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16675 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3]
def baseStart_16675 : Nat := 118140960795 + 16675 * 2 ^ 59
def prefixEnd_16675 : Nat := 4983230072969 + 3 ^ 40 * 16675 * 2
def baseEnd_16675 : Nat := 8562289913827492685819

theorem tailTrace_16675 : CollatzResearch.WordTrace tailWord_16675 prefixEnd_16675 8562289913827492685819 := by
  unfold tailWord_16675
  simp only [CollatzResearch.WordTrace]
  refine ⟨608187214596797708379479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 405458143064531805586319 608187214596797708379479)
  ·
    refine ⟨912280821895196562569219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 608187214596797708379479 912280821895196562569219)
    ·
      refine ⟨1368421232842794843853829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 912280821895196562569219 1368421232842794843853829)
      ·
        refine ⟨256578981158024033222593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1368421232842794843853829 256578981158024033222593)
        ·
          refine ⟨192434235868518024916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256578981158024033222593 192434235868518024916945)
          ·
            refine ⟨144325676901388518687709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192434235868518024916945 144325676901388518687709)
            ·
              refine ⟨54122128838020694507891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144325676901388518687709 54122128838020694507891)
              ·
                refine ⟨81183193257031041761837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54122128838020694507891 81183193257031041761837)
                ·
                  refine ⟨30443697471386640660689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81183193257031041761837 30443697471386640660689)
                  ·
                    refine ⟨22832773103539980495517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30443697471386640660689 22832773103539980495517)
                    ·
                      refine ⟨8562289913827492685819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 22832773103539980495517 8562289913827492685819)
                      ·
                        rfl

theorem cell23_16675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_16675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16675 prefixEnd_16675 := by exact prefixLift 16675
  have htrace : WordTrace (prefixWord ++ tailWord_16675) baseStart_16675 baseEnd_16675 := by
    simpa [prefixWord, tailWord_16675, baseEnd_16675] using wordTrace_append hprefix tailTrace_16675
  have hstable : (prefixWord ++ tailWord_16675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16675).length < 2 ^ (prefixWord ++ tailWord_16675).sum := by decide
  have hdescent : baseEnd_16675 < baseStart_16675 := by decide
  rcases family_descends (prefixWord ++ tailWord_16675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16682 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_16682 : Nat := 118140960795 + 16682 * 2 ^ 59
def prefixEnd_16682 : Nat := 4983230072969 + 3 ^ 40 * 16682 * 2
def baseEnd_16682 : Nat := 2855294759469655099429

theorem tailTrace_16682 : CollatzResearch.WordTrace tailWord_16682 prefixEnd_16682 2855294759469655099429 := by
  unfold tailWord_16682
  simp only [CollatzResearch.WordTrace]
  refine ⟨152110631392859475971075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 405628350380958602589533 152110631392859475971075)
  ·
    refine ⟨228165947089289213956613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152110631392859475971075 228165947089289213956613)
    ·
      refine ⟨42781115079241727616865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 228165947089289213956613 42781115079241727616865)
      ·
        refine ⟨32085836309431295712649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42781115079241727616865 32085836309431295712649)
        ·
          refine ⟨24064377232073471784487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32085836309431295712649 24064377232073471784487)
          ·
            refine ⟨36096565848110207676731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24064377232073471784487 36096565848110207676731)
            ·
              refine ⟨54144848772165311515097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36096565848110207676731 54144848772165311515097)
              ·
                refine ⟨40608636579123983636323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54144848772165311515097 40608636579123983636323)
                ·
                  refine ⟨60912954868685975454485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40608636579123983636323 60912954868685975454485)
                  ·
                    refine ⟨2855294759469655099429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60912954868685975454485 2855294759469655099429)
                    ·
                      rfl

theorem cell23_16682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_16682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16682 prefixEnd_16682 := by exact prefixLift 16682
  have htrace : WordTrace (prefixWord ++ tailWord_16682) baseStart_16682 baseEnd_16682 := by
    simpa [prefixWord, tailWord_16682, baseEnd_16682] using wordTrace_append hprefix tailTrace_16682
  have hstable : (prefixWord ++ tailWord_16682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16682).length < 2 ^ (prefixWord ++ tailWord_16682).sum := by decide
  have hdescent : baseEnd_16682 < baseStart_16682 := by decide
  rcases family_descends (prefixWord ++ tailWord_16682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16686 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_16686 : Nat := 118140960795 + 16686 * 2 ^ 59
def prefixEnd_16686 : Nat := 4983230072969 + 3 ^ 40 * 16686 * 2
def baseEnd_16686 : Nat := 2855979400342316549423

theorem tailTrace_16686 : CollatzResearch.WordTrace tailWord_16686 prefixEnd_16686 2855979400342316549423 := by
  unfold tailWord_16686
  simp only [CollatzResearch.WordTrace]
  refine ⟨76073552194618323378739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 405725611704631058019941 76073552194618323378739)
  ·
    refine ⟨114110328291927485068109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76073552194618323378739 114110328291927485068109)
    ·
      refine ⟨42791373109472806900541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114110328291927485068109 42791373109472806900541)
      ·
        refine ⟨16046764916052302587703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42791373109472806900541 16046764916052302587703)
        ·
          refine ⟨24070147374078453881555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16046764916052302587703 24070147374078453881555)
          ·
            refine ⟨36105221061117680822333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24070147374078453881555 36105221061117680822333)
            ·
              refine ⟨13539457897919130308375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36105221061117680822333 13539457897919130308375)
              ·
                refine ⟨20309186846878695462563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13539457897919130308375 20309186846878695462563)
                ·
                  refine ⟨30463780270318043193845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20309186846878695462563 30463780270318043193845)
                  ·
                    refine ⟨2855979400342316549423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30463780270318043193845 2855979400342316549423)
                    ·
                      rfl

theorem cell23_16686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_16686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16686 prefixEnd_16686 := by exact prefixLift 16686
  have htrace : WordTrace (prefixWord ++ tailWord_16686) baseStart_16686 baseEnd_16686 := by
    simpa [prefixWord, tailWord_16686, baseEnd_16686] using wordTrace_append hprefix tailTrace_16686
  have hstable : (prefixWord ++ tailWord_16686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16686).length < 2 ^ (prefixWord ++ tailWord_16686).sum := by decide
  have hdescent : baseEnd_16686 < baseStart_16686 := by decide
  rcases family_descends (prefixWord ++ tailWord_16686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16689 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_16689 : Nat := 118140960795 + 16689 * 2 ^ 59
def prefixEnd_16689 : Nat := 4983230072969 + 3 ^ 40 * 16689 * 2
def baseEnd_16689 : Nat := 8569478642990437910755

theorem tailTrace_16689 : CollatzResearch.WordTrace tailWord_16689 prefixEnd_16689 8569478642990437910755 := by
  unfold tailWord_16689
  simp only [CollatzResearch.WordTrace]
  refine ⟨608697836546078099389121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 405798557697385399592747 608697836546078099389121)
  ·
    refine ⟨456523377409558574541841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 608697836546078099389121 456523377409558574541841)
    ·
      refine ⟨342392533057168930906381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456523377409558574541841 342392533057168930906381)
      ·
        refine ⟨128397199896438349089893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 342392533057168930906381 128397199896438349089893)
        ·
          refine ⟨24074474980582190454355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128397199896438349089893 24074474980582190454355)
          ·
            refine ⟨36111712470873285681533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24074474980582190454355 36111712470873285681533)
            ·
              refine ⟨13541892176577482130575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36111712470873285681533 13541892176577482130575)
              ·
                refine ⟨20312838264866223195863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13541892176577482130575 20312838264866223195863)
                ·
                  refine ⟨30469257397299334793795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20312838264866223195863 30469257397299334793795)
                  ·
                    refine ⟨45703886095949002190693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30469257397299334793795 45703886095949002190693)
                    ·
                      refine ⟨8569478642990437910755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 45703886095949002190693 8569478642990437910755)
                      ·
                        rfl

theorem cell23_16689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_16689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16689 prefixEnd_16689 := by exact prefixLift 16689
  have htrace : WordTrace (prefixWord ++ tailWord_16689) baseStart_16689 baseEnd_16689 := by
    simpa [prefixWord, tailWord_16689, baseEnd_16689] using wordTrace_append hprefix tailTrace_16689
  have hstable : (prefixWord ++ tailWord_16689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16689).length < 2 ^ (prefixWord ++ tailWord_16689).sum := by decide
  have hdescent : baseEnd_16689 < baseStart_16689 := by decide
  rcases family_descends (prefixWord ++ tailWord_16689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16692 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_16692 : Nat := 118140960795 + 16692 * 2 ^ 59
def prefixEnd_16692 : Nat := 4983230072969 + 3 ^ 40 * 16692 * 2
def baseEnd_16692 : Nat := 8571019084953926173241

theorem tailTrace_16692 : CollatzResearch.WordTrace tailWord_16692 prefixEnd_16692 8571019084953926173241 := by
  unfold tailWord_16692
  simp only [CollatzResearch.WordTrace]
  refine ⟨304403627767604805874165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 405871503690139741165553 304403627767604805874165)
  ·
    refine ⟨28537840103212950550703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 304403627767604805874165 28537840103212950550703)
    ·
      refine ⟨42806760154819425826055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28537840103212950550703 42806760154819425826055)
      ·
        refine ⟨64210140232229138739083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42806760154819425826055 64210140232229138739083)
        ·
          refine ⟨96315210348343708108625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64210140232229138739083 96315210348343708108625)
          ·
            refine ⟨72236407761257781081469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96315210348343708108625 72236407761257781081469)
            ·
              refine ⟨27088652910471667905551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72236407761257781081469 27088652910471667905551)
              ·
                refine ⟨40632979365707501858327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27088652910471667905551 40632979365707501858327)
                ·
                  refine ⟨60949469048561252787491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40632979365707501858327 60949469048561252787491)
                  ·
                    refine ⟨91424203572841879181237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60949469048561252787491 91424203572841879181237)
                    ·
                      refine ⟨8571019084953926173241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 91424203572841879181237 8571019084953926173241)
                      ·
                        rfl

theorem cell23_16692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_16692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16692 prefixEnd_16692 := by exact prefixLift 16692
  have htrace : WordTrace (prefixWord ++ tailWord_16692) baseStart_16692 baseEnd_16692 := by
    simpa [prefixWord, tailWord_16692, baseEnd_16692] using wordTrace_append hprefix tailTrace_16692
  have hstable : (prefixWord ++ tailWord_16692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16692).length < 2 ^ (prefixWord ++ tailWord_16692).sum := by decide
  have hdescent : baseEnd_16692 < baseStart_16692 := by decide
  rcases family_descends (prefixWord ++ tailWord_16692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16749 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_16749 : Nat := 118140960795 + 16749 * 2 ^ 59
def prefixEnd_16749 : Nat := 4983230072969 + 3 ^ 40 * 16749 * 2
def baseEnd_16749 : Nat := 8600287482260203160479

theorem tailTrace_16749 : CollatzResearch.WordTrace tailWord_16749 prefixEnd_16749 8600287482260203160479 := by
  unfold tailWord_16749
  simp only [CollatzResearch.WordTrace]
  refine ⟨610886216328708346573301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407257477552472231048867 610886216328708346573301)
  ·
    refine ⟨57270582780816407491247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 610886216328708346573301 57270582780816407491247)
    ·
      refine ⟨85905874171224611236871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57270582780816407491247 85905874171224611236871)
      ·
        refine ⟨128858811256836916855307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85905874171224611236871 128858811256836916855307)
        ·
          refine ⟨193288216885255375282961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128858811256836916855307 193288216885255375282961)
          ·
            refine ⟨144966162663941531462221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193288216885255375282961 144966162663941531462221)
            ·
              refine ⟨54362310998978074298333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144966162663941531462221 54362310998978074298333)
              ·
                refine ⟨20385866624616777861875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54362310998978074298333 20385866624616777861875)
                ·
                  refine ⟨30578799936925166792813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20385866624616777861875 30578799936925166792813)
                  ·
                    refine ⟨11467049976346937547305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30578799936925166792813 11467049976346937547305)
                    ·
                      refine ⟨8600287482260203160479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11467049976346937547305 8600287482260203160479)
                      ·
                        rfl

theorem cell23_16749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_16749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16749 prefixEnd_16749 := by exact prefixLift 16749
  have htrace : WordTrace (prefixWord ++ tailWord_16749) baseStart_16749 baseEnd_16749 := by
    simpa [prefixWord, tailWord_16749, baseEnd_16749] using wordTrace_append hprefix tailTrace_16749
  have hstable : (prefixWord ++ tailWord_16749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16749).length < 2 ^ (prefixWord ++ tailWord_16749).sum := by decide
  have hdescent : baseEnd_16749 < baseStart_16749 := by decide
  rcases family_descends (prefixWord ++ tailWord_16749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16775 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_16775 : Nat := 118140960795 + 16775 * 2 ^ 59
def prefixEnd_16775 : Nat := 4983230072969 + 3 ^ 40 * 16775 * 2
def baseEnd_16775 : Nat := 8613637979277101435359

theorem tailTrace_16775 : CollatzResearch.WordTrace tailWord_16775 prefixEnd_16775 8613637979277101435359 := by
  unfold tailWord_16775
  simp only [CollatzResearch.WordTrace]
  refine ⟨611834514234514787019779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407889676156343191346519 611834514234514787019779)
  ·
    refine ⟨917751771351772180529669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611834514234514787019779 917751771351772180529669)
    ·
      refine ⟨172078457128457283849313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 917751771351772180529669 172078457128457283849313)
      ·
        refine ⟨129058842846342962886985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172078457128457283849313 129058842846342962886985)
        ·
          refine ⟨96794132134757222165239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129058842846342962886985 96794132134757222165239)
          ·
            refine ⟨145191198202135833247859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96794132134757222165239 145191198202135833247859)
            ·
              refine ⟨217786797303203749871789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145191198202135833247859 217786797303203749871789)
              ·
                refine ⟨81670048988701406201921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217786797303203749871789 81670048988701406201921)
                ·
                  refine ⟨61252536741526054651441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81670048988701406201921 61252536741526054651441)
                  ·
                    refine ⟨45939402556144540988581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61252536741526054651441 45939402556144540988581)
                    ·
                      refine ⟨8613637979277101435359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 45939402556144540988581 8613637979277101435359)
                      ·
                        rfl

theorem cell23_16775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_16775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16775 prefixEnd_16775 := by exact prefixLift 16775
  have htrace : WordTrace (prefixWord ++ tailWord_16775) baseStart_16775 baseEnd_16775 := by
    simpa [prefixWord, tailWord_16775, baseEnd_16775] using wordTrace_append hprefix tailTrace_16775
  have hstable : (prefixWord ++ tailWord_16775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16775).length < 2 ^ (prefixWord ++ tailWord_16775).sum := by decide
  have hdescent : baseEnd_16775 < baseStart_16775 := by decide
  rcases family_descends (prefixWord ++ tailWord_16775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16779 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 4, 2]
def baseStart_16779 : Nat := 118140960795 + 16779 * 2 ^ 59
def prefixEnd_16779 : Nat := 4983230072969 + 3 ^ 40 * 16779 * 2
def baseEnd_16779 : Nat := 8615691901895085785341

theorem tailTrace_16779 : CollatzResearch.WordTrace tailWord_16779 prefixEnd_16779 8615691901895085785341 := by
  unfold tailWord_16779
  simp only [CollatzResearch.WordTrace]
  refine ⟨611980406220023470165391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 407986937480015646776927 611980406220023470165391)
  ·
    refine ⟨917970609330035205248087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 611980406220023470165391 917970609330035205248087)
    ·
      refine ⟨1376955913995052807872131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 917970609330035205248087 1376955913995052807872131)
      ·
        refine ⟨2065433870992579211808197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376955913995052807872131 2065433870992579211808197)
        ·
          refine ⟨387268850811108602214037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2065433870992579211808197 387268850811108602214037)
          ·
            refine ⟨18153227381770715728783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 387268850811108602214037 18153227381770715728783)
            ·
              refine ⟨27229841072656073593175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18153227381770715728783 27229841072656073593175)
              ·
                refine ⟨40844761608984110389763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27229841072656073593175 40844761608984110389763)
                ·
                  refine ⟨61267142413476165584645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40844761608984110389763 61267142413476165584645)
                  ·
                    refine ⟨11487589202526781047121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61267142413476165584645 11487589202526781047121)
                    ·
                      refine ⟨8615691901895085785341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11487589202526781047121 8615691901895085785341)
                      ·
                        rfl

theorem cell23_16779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 4, 2].length) (baseStart_16779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16779 prefixEnd_16779 := by exact prefixLift 16779
  have htrace : WordTrace (prefixWord ++ tailWord_16779) baseStart_16779 baseEnd_16779 := by
    simpa [prefixWord, tailWord_16779, baseEnd_16779] using wordTrace_append hprefix tailTrace_16779
  have hstable : (prefixWord ++ tailWord_16779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16779).length < 2 ^ (prefixWord ++ tailWord_16779).sum := by decide
  have hdescent : baseEnd_16779 < baseStart_16779 := by decide
  rcases family_descends (prefixWord ++ tailWord_16779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16825 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_16825 : Nat := 118140960795 + 16825 * 2 ^ 59
def prefixEnd_16825 : Nat := 4983230072969 + 3 ^ 40 * 16825 * 2
def baseEnd_16825 : Nat := 8639312012001905810129

theorem tailTrace_16825 : CollatzResearch.WordTrace tailWord_16825 prefixEnd_16825 8639312012001905810129 := by
  unfold tailWord_16825
  simp only [CollatzResearch.WordTrace]
  refine ⟨613658164053373326339929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 409105442702248884226619 613658164053373326339929)
  ·
    refine ⟨460243623040029994754947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 613658164053373326339929 460243623040029994754947)
    ·
      refine ⟨690365434560044992132421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460243623040029994754947 690365434560044992132421)
      ·
        refine ⟨129443518980008436024829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 690365434560044992132421 129443518980008436024829)
        ·
          refine ⟨48541319617503163509311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129443518980008436024829 48541319617503163509311)
          ·
            refine ⟨72811979426254745263967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48541319617503163509311 72811979426254745263967)
            ·
              refine ⟨109217969139382117895951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72811979426254745263967 109217969139382117895951)
              ·
                refine ⟨163826953709073176843927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109217969139382117895951 163826953709073176843927)
                ·
                  refine ⟨245740430563609765265891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163826953709073176843927 245740430563609765265891)
                  ·
                    refine ⟨368610645845414647898837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 245740430563609765265891 368610645845414647898837)
                    ·
                      refine ⟨8639312012001905810129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 368610645845414647898837 8639312012001905810129)
                      ·
                        rfl

theorem cell23_16825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_16825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16825 prefixEnd_16825 := by exact prefixLift 16825
  have htrace : WordTrace (prefixWord ++ tailWord_16825) baseStart_16825 baseEnd_16825 := by
    simpa [prefixWord, tailWord_16825, baseEnd_16825] using wordTrace_append hprefix tailTrace_16825
  have hstable : (prefixWord ++ tailWord_16825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16825).length < 2 ^ (prefixWord ++ tailWord_16825).sum := by decide
  have hdescent : baseEnd_16825 < baseStart_16825 := by decide
  rcases family_descends (prefixWord ++ tailWord_16825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16835 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4]
def baseStart_16835 : Nat := 118140960795 + 16835 * 2 ^ 59
def prefixEnd_16835 : Nat := 4983230072969 + 3 ^ 40 * 16835 * 2
def baseEnd_16835 : Nat := 8644446818546866685083

theorem tailTrace_16835 : CollatzResearch.WordTrace tailWord_16835 prefixEnd_16835 8644446818546866685083 := by
  unfold tailWord_16835
  simp only [CollatzResearch.WordTrace]
  refine ⟨614022894017145034203959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 409348596011430022802639 614022894017145034203959)
  ·
    refine ⟨921034341025717551305939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 614022894017145034203959 921034341025717551305939)
    ·
      refine ⟨1381551511538576326958909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921034341025717551305939 1381551511538576326958909)
      ·
        refine ⟨518081816826966122609591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1381551511538576326958909 518081816826966122609591)
        ·
          refine ⟨777122725240449183914387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518081816826966122609591 777122725240449183914387)
          ·
            refine ⟨1165684087860673775871581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777122725240449183914387 1165684087860673775871581)
            ·
              refine ⟨437131532947752665951843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1165684087860673775871581 437131532947752665951843)
              ·
                refine ⟨655697299421628998927765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437131532947752665951843 655697299421628998927765)
                ·
                  refine ⟨30735810910388859324739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655697299421628998927765 30735810910388859324739)
                  ·
                    refine ⟨46103716365583288987109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30735810910388859324739 46103716365583288987109)
                    ·
                      refine ⟨8644446818546866685083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 46103716365583288987109 8644446818546866685083)
                      ·
                        rfl

theorem cell23_16835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_16835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16835 prefixEnd_16835 := by exact prefixLift 16835
  have htrace : WordTrace (prefixWord ++ tailWord_16835) baseStart_16835 baseEnd_16835 := by
    simpa [prefixWord, tailWord_16835, baseEnd_16835] using wordTrace_append hprefix tailTrace_16835
  have hstable : (prefixWord ++ tailWord_16835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16835).length < 2 ^ (prefixWord ++ tailWord_16835).sum := by decide
  have hdescent : baseEnd_16835 < baseStart_16835 := by decide
  rcases family_descends (prefixWord ++ tailWord_16835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16865 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_16865 : Nat := 118140960795 + 16865 * 2 ^ 59
def prefixEnd_16865 : Nat := 4983230072969 + 3 ^ 40 * 16865 * 2
def baseEnd_16865 : Nat := 8659851238181749309945

theorem tailTrace_16865 : CollatzResearch.WordTrace tailWord_16865 prefixEnd_16865 8659851238181749309945 := by
  unfold tailWord_16865
  simp only [CollatzResearch.WordTrace]
  refine ⟨615117083908460157796049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 410078055938973438530699 615117083908460157796049)
  ·
    refine ⟨461337812931345118347037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 615117083908460157796049 461337812931345118347037)
    ·
      refine ⟨173001679849254419380139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 461337812931345118347037 173001679849254419380139)
      ·
        refine ⟨259502519773881629070209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173001679849254419380139 259502519773881629070209)
        ·
          refine ⟨194626889830411221802657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259502519773881629070209 194626889830411221802657)
          ·
            refine ⟨145970167372808416351993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194626889830411221802657 145970167372808416351993)
            ·
              refine ⟨109477625529606312263995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145970167372808416351993 109477625529606312263995)
              ·
                refine ⟨164216438294409468395993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109477625529606312263995 164216438294409468395993)
                ·
                  refine ⟨123162328720807101296995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164216438294409468395993 123162328720807101296995)
                  ·
                    refine ⟨184743493081210651945493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123162328720807101296995 184743493081210651945493)
                    ·
                      refine ⟨8659851238181749309945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 184743493081210651945493 8659851238181749309945)
                      ·
                        rfl

theorem cell23_16865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_16865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16865 prefixEnd_16865 := by exact prefixLift 16865
  have htrace : WordTrace (prefixWord ++ tailWord_16865) baseStart_16865 baseEnd_16865 := by
    simpa [prefixWord, tailWord_16865, baseEnd_16865] using wordTrace_append hprefix tailTrace_16865
  have hstable : (prefixWord ++ tailWord_16865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16865).length < 2 ^ (prefixWord ++ tailWord_16865).sum := by decide
  have hdescent : baseEnd_16865 < baseStart_16865 := by decide
  rcases family_descends (prefixWord ++ tailWord_16865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16929 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_16929 : Nat := 118140960795 + 16929 * 2 ^ 59
def prefixEnd_16929 : Nat := 4983230072969 + 3 ^ 40 * 16929 * 2
def baseEnd_16929 : Nat := 8692714000069498909651

theorem tailTrace_16929 : CollatzResearch.WordTrace tailWord_16929 prefixEnd_16929 8692714000069498909651 := by
  unfold tailWord_16929
  simp only [CollatzResearch.WordTrace]
  refine ⟨617451355676599088125841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 411634237117732725417227 617451355676599088125841)
  ·
    refine ⟨463088516757449316094381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 617451355676599088125841 463088516757449316094381)
    ·
      refine ⟨173658193784043493535393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 463088516757449316094381 173658193784043493535393)
      ·
        refine ⟨130243645338032620151545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173658193784043493535393 130243645338032620151545)
        ·
          refine ⟨97682734003524465113659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130243645338032620151545 97682734003524465113659)
          ·
            refine ⟨146524101005286697670489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97682734003524465113659 146524101005286697670489)
            ·
              refine ⟨109893075753965023252867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146524101005286697670489 109893075753965023252867)
              ·
                refine ⟨164839613630947534879301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109893075753965023252867 164839613630947534879301)
                ·
                  refine ⟨30907427555802662789869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164839613630947534879301 30907427555802662789869)
                  ·
                    refine ⟨11590285333425998546201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30907427555802662789869 11590285333425998546201)
                    ·
                      refine ⟨8692714000069498909651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11590285333425998546201 8692714000069498909651)
                      ·
                        rfl

theorem cell23_16929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_16929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16929 prefixEnd_16929 := by exact prefixLift 16929
  have htrace : WordTrace (prefixWord ++ tailWord_16929) baseStart_16929 baseEnd_16929 := by
    simpa [prefixWord, tailWord_16929, baseEnd_16929] using wordTrace_append hprefix tailTrace_16929
  have hstable : (prefixWord ++ tailWord_16929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16929).length < 2 ^ (prefixWord ++ tailWord_16929).sum := by decide
  have hdescent : baseEnd_16929 < baseStart_16929 := by decide
  rcases family_descends (prefixWord ++ tailWord_16929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16936 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_16936 : Nat := 118140960795 + 16936 * 2 ^ 59
def prefixEnd_16936 : Nat := 4983230072969 + 3 ^ 40 * 16936 * 2
def baseEnd_16936 : Nat := 8696308364650971522119

theorem tailTrace_16936 : CollatzResearch.WordTrace tailWord_16936 prefixEnd_16936 8696308364650971522119 := by
  unfold tailWord_16936
  simp only [CollatzResearch.WordTrace]
  refine ⟨308853333325619641815331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 411804444434159522420441 308853333325619641815331)
  ·
    refine ⟨463279999988429462722997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 308853333325619641815331 463279999988429462722997)
    ·
      refine ⟨43432499998915262130281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 463279999988429462722997 43432499998915262130281)
      ·
        refine ⟨32574374999186446597711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43432499998915262130281 32574374999186446597711)
        ·
          refine ⟨48861562498779669896567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32574374999186446597711 48861562498779669896567)
          ·
            refine ⟨73292343748169504844851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48861562498779669896567 73292343748169504844851)
            ·
              refine ⟨109938515622254257267277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73292343748169504844851 109938515622254257267277)
              ·
                refine ⟨41226943358345346475229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109938515622254257267277 41226943358345346475229)
                ·
                  refine ⟨15460103759379504928211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41226943358345346475229 15460103759379504928211)
                  ·
                    refine ⟨23190155639069257392317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15460103759379504928211 23190155639069257392317)
                    ·
                      refine ⟨8696308364650971522119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 23190155639069257392317 8696308364650971522119)
                      ·
                        rfl

theorem cell23_16936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_16936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16936 prefixEnd_16936 := by exact prefixLift 16936
  have htrace : WordTrace (prefixWord ++ tailWord_16936) baseStart_16936 baseEnd_16936 := by
    simpa [prefixWord, tailWord_16936, baseEnd_16936] using wordTrace_append hprefix tailTrace_16936
  have hstable : (prefixWord ++ tailWord_16936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16936).length < 2 ^ (prefixWord ++ tailWord_16936).sum := by decide
  have hdescent : baseEnd_16936 < baseStart_16936 := by decide
  rcases family_descends (prefixWord ++ tailWord_16936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16959 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 4]
def baseStart_16959 : Nat := 118140960795 + 16959 * 2 ^ 59
def prefixEnd_16959 : Nat := 4983230072969 + 3 ^ 40 * 16959 * 2
def baseEnd_16959 : Nat := 8708118419704381534513

theorem tailTrace_16959 : CollatzResearch.WordTrace tailWord_16959 prefixEnd_16959 8708118419704381534513 := by
  unfold tailWord_16959
  simp only [CollatzResearch.WordTrace]
  refine ⟨618545545567914211717931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 412363697045276141145287 618545545567914211717931)
  ·
    refine ⟨927818318351871317576897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 618545545567914211717931 927818318351871317576897)
    ·
      refine ⟨695863738763903488182673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927818318351871317576897 695863738763903488182673)
      ·
        refine ⟨521897804072927616137005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695863738763903488182673 521897804072927616137005)
        ·
          refine ⟨195711676527347856051377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521897804072927616137005 195711676527347856051377)
          ·
            refine ⟨146783757395510892038533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195711676527347856051377 146783757395510892038533)
            ·
              refine ⟨27521954511658292257225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146783757395510892038533 27521954511658292257225)
              ·
                refine ⟨20641465883743719192919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27521954511658292257225 20641465883743719192919)
                ·
                  refine ⟨30962198825615578789379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20641465883743719192919 30962198825615578789379)
                  ·
                    refine ⟨46443298238423368184069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30962198825615578789379 46443298238423368184069)
                    ·
                      refine ⟨8708118419704381534513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 46443298238423368184069 8708118419704381534513)
                      ·
                        rfl

theorem cell23_16959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_16959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16959 prefixEnd_16959 := by exact prefixLift 16959
  have htrace : WordTrace (prefixWord ++ tailWord_16959) baseStart_16959 baseEnd_16959 := by
    simpa [prefixWord, tailWord_16959, baseEnd_16959] using wordTrace_append hprefix tailTrace_16959
  have hstable : (prefixWord ++ tailWord_16959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16959).length < 2 ^ (prefixWord ++ tailWord_16959).sum := by decide
  have hdescent : baseEnd_16959 < baseStart_16959 := by decide
  rcases family_descends (prefixWord ++ tailWord_16959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16964 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_16964 : Nat := 118140960795 + 16964 * 2 ^ 59
def prefixEnd_16964 : Nat := 4983230072969 + 3 ^ 40 * 16964 * 2
def baseEnd_16964 : Nat := 2903561940992287323997

theorem tailTrace_16964 : CollatzResearch.WordTrace tailWord_16964 prefixEnd_16964 2903561940992287323997 := by
  unfold tailWord_16964
  simp only [CollatzResearch.WordTrace]
  refine ⟨309363955274900032824973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 412485273699866710433297 309363955274900032824973)
  ·
    refine ⟨116011483228087512309365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 309363955274900032824973 116011483228087512309365)
    ·
      refine ⟨10876076552633204279003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 116011483228087512309365 10876076552633204279003)
      ·
        refine ⟨16314114828949806418505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10876076552633204279003 16314114828949806418505)
        ·
          refine ⟨12235586121712354813879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16314114828949806418505 12235586121712354813879)
          ·
            refine ⟨18353379182568532220819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12235586121712354813879 18353379182568532220819)
            ·
              refine ⟨27530068773852798331229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18353379182568532220819 27530068773852798331229)
              ·
                refine ⟨10323775790194799374211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27530068773852798331229 10323775790194799374211)
                ·
                  refine ⟨15485663685292199061317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10323775790194799374211 15485663685292199061317)
                  ·
                    refine ⟨2903561940992287323997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15485663685292199061317 2903561940992287323997)
                    ·
                      rfl

theorem cell23_16964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_16964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16964 prefixEnd_16964 := by exact prefixLift 16964
  have htrace : WordTrace (prefixWord ++ tailWord_16964) baseStart_16964 baseEnd_16964 := by
    simpa [prefixWord, tailWord_16964, baseEnd_16964] using wordTrace_append hprefix tailTrace_16964
  have hstable : (prefixWord ++ tailWord_16964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16964).length < 2 ^ (prefixWord ++ tailWord_16964).sum := by decide
  have hdescent : baseEnd_16964 < baseStart_16964 := by decide
  rcases family_descends (prefixWord ++ tailWord_16964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16972 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_16972 : Nat := 118140960795 + 16972 * 2 ^ 59
def prefixEnd_16972 : Nat := 4983230072969 + 3 ^ 40 * 16972 * 2
def baseEnd_16972 : Nat := 8714793668212830671953

theorem tailTrace_16972 : CollatzResearch.WordTrace tailWord_16972 prefixEnd_16972 8714793668212830671953 := by
  unfold tailWord_16972
  simp only [CollatzResearch.WordTrace]
  refine ⟨309509847260408715970585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 412679796347211621294113 309509847260408715970585)
  ·
    refine ⟨232132385445306536977939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 309509847260408715970585 232132385445306536977939)
    ·
      refine ⟨348198578167959805466909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232132385445306536977939 348198578167959805466909)
      ·
        refine ⟨130574466812984927050091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 348198578167959805466909 130574466812984927050091)
        ·
          refine ⟨195861700219477390575137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130574466812984927050091 195861700219477390575137)
          ·
            refine ⟨146896275164608042931353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195861700219477390575137 146896275164608042931353)
            ·
              refine ⟨110172206373456032198515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146896275164608042931353 110172206373456032198515)
              ·
                refine ⟨165258309560184048297773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110172206373456032198515 165258309560184048297773)
                ·
                  refine ⟨61971866085069018111665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165258309560184048297773 61971866085069018111665)
                  ·
                    refine ⟨46478899563801763583749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61971866085069018111665 46478899563801763583749)
                    ·
                      refine ⟨8714793668212830671953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 46478899563801763583749 8714793668212830671953)
                      ·
                        rfl

theorem cell23_16972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_16972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16972 prefixEnd_16972 := by exact prefixLift 16972
  have htrace : WordTrace (prefixWord ++ tailWord_16972) baseStart_16972 baseEnd_16972 := by
    simpa [prefixWord, tailWord_16972, baseEnd_16972] using wordTrace_append hprefix tailTrace_16972
  have hstable : (prefixWord ++ tailWord_16972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16972).length < 2 ^ (prefixWord ++ tailWord_16972).sum := by decide
  have hdescent : baseEnd_16972 < baseStart_16972 := by decide
  rcases family_descends (prefixWord ++ tailWord_16972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16993 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_16993 : Nat := 118140960795 + 16993 * 2 ^ 59
def prefixEnd_16993 : Nat := 4983230072969 + 3 ^ 40 * 16993 * 2
def baseEnd_16993 : Nat := 8725576761957248509357

theorem tailTrace_16993 : CollatzResearch.WordTrace tailWord_16993 prefixEnd_16993 8725576761957248509357 := by
  unfold tailWord_16993
  simp only [CollatzResearch.WordTrace]
  refine ⟨619785627444738018455633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 413190418296492012303755 619785627444738018455633)
  ·
    refine ⟨464839220583553513841725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 619785627444738018455633 464839220583553513841725)
    ·
      refine ⟨174314707718832567690647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 464839220583553513841725 174314707718832567690647)
      ·
        refine ⟨261472061578248851535971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 174314707718832567690647 261472061578248851535971)
        ·
          refine ⟨392208092367373277303957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261472061578248851535971 392208092367373277303957)
          ·
            refine ⟨18384754329720622373623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 392208092367373277303957 18384754329720622373623)
            ·
              refine ⟨27577131494580933560435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18384754329720622373623 27577131494580933560435)
              ·
                refine ⟨41365697241871400340653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27577131494580933560435 41365697241871400340653)
                ·
                  refine ⟨15512136465701775127745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41365697241871400340653 15512136465701775127745)
                  ·
                    refine ⟨11634102349276331345809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15512136465701775127745 11634102349276331345809)
                    ·
                      refine ⟨8725576761957248509357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11634102349276331345809 8725576761957248509357)
                      ·
                        rfl

theorem cell23_16993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_16993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_16993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_16993 prefixEnd_16993 := by exact prefixLift 16993
  have htrace : WordTrace (prefixWord ++ tailWord_16993) baseStart_16993 baseEnd_16993 := by
    simpa [prefixWord, tailWord_16993, baseEnd_16993] using wordTrace_append hprefix tailTrace_16993
  have hstable : (prefixWord ++ tailWord_16993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16993).length < 2 ^ (prefixWord ++ tailWord_16993).sum := by decide
  have hdescent : baseEnd_16993 < baseStart_16993 := by decide
  rcases family_descends (prefixWord ++ tailWord_16993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17002 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_17002 : Nat := 118140960795 + 17002 * 2 ^ 59
def prefixEnd_17002 : Nat := 4983230072969 + 3 ^ 40 * 17002 * 2
def baseEnd_17002 : Nat := 8730198087847713296815

theorem tailTrace_17002 : CollatzResearch.WordTrace tailWord_17002 prefixEnd_17002 8730198087847713296815 := by
  unfold tailWord_17002
  simp only [CollatzResearch.WordTrace]
  refine ⟨155028471103033138883315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 413409256274755037022173 155028471103033138883315)
  ·
    refine ⟨232542706654549708324973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 155028471103033138883315 232542706654549708324973)
    ·
      refine ⟨87203514995456140621865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 232542706654549708324973 87203514995456140621865)
      ·
        refine ⟨65402636246592105466399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87203514995456140621865 65402636246592105466399)
        ·
          refine ⟨98103954369888158199599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65402636246592105466399 98103954369888158199599)
          ·
            refine ⟨147155931554832237299399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98103954369888158199599 147155931554832237299399)
            ·
              refine ⟨220733897332248355949099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147155931554832237299399 220733897332248355949099)
              ·
                refine ⟨331100845998372533923649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220733897332248355949099 331100845998372533923649)
                ·
                  refine ⟨248325634498779400442737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 331100845998372533923649 248325634498779400442737)
                  ·
                    refine ⟨186244225874084550332053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 248325634498779400442737 186244225874084550332053)
                    ·
                      refine ⟨8730198087847713296815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 186244225874084550332053 8730198087847713296815)
                      ·
                        rfl

theorem cell23_17002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_17002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17002 prefixEnd_17002 := by exact prefixLift 17002
  have htrace : WordTrace (prefixWord ++ tailWord_17002) baseStart_17002 baseEnd_17002 := by
    simpa [prefixWord, tailWord_17002, baseEnd_17002] using wordTrace_append hprefix tailTrace_17002
  have hstable : (prefixWord ++ tailWord_17002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17002).length < 2 ^ (prefixWord ++ tailWord_17002).sum := by decide
  have hdescent : baseEnd_17002 < baseStart_17002 := by decide
  rcases family_descends (prefixWord ++ tailWord_17002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17044 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_17044 : Nat := 118140960795 + 17044 * 2 ^ 59
def prefixEnd_17044 : Nat := 4983230072969 + 3 ^ 40 * 17044 * 2
def baseEnd_17044 : Nat := 8751764275336548971623

theorem tailTrace_17044 : CollatzResearch.WordTrace tailWord_17044 prefixEnd_17044 8751764275336548971623 := by
  unfold tailWord_17044
  simp only [CollatzResearch.WordTrace]
  refine ⟨310822875129986864281093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 414430500173315819041457 310822875129986864281093)
  ·
    refine ⟨58279289086872537052705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 310822875129986864281093 58279289086872537052705)
    ·
      refine ⟨43709466815154402789529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58279289086872537052705 43709466815154402789529)
      ·
        refine ⟨32782100111365802092147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43709466815154402789529 32782100111365802092147)
        ·
          refine ⟨49173150167048703138221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32782100111365802092147 49173150167048703138221)
          ·
            refine ⟨18439931312643263676833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49173150167048703138221 18439931312643263676833)
            ·
              refine ⟨13829948484482447757625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18439931312643263676833 13829948484482447757625)
              ·
                refine ⟨10372461363361835818219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13829948484482447757625 10372461363361835818219)
                ·
                  refine ⟨15558692045042753727329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10372461363361835818219 15558692045042753727329)
                  ·
                    refine ⟨11669019033782065295497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15558692045042753727329 11669019033782065295497)
                    ·
                      refine ⟨8751764275336548971623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11669019033782065295497 8751764275336548971623)
                      ·
                        rfl

theorem cell23_17044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_17044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17044 prefixEnd_17044 := by exact prefixLift 17044
  have htrace : WordTrace (prefixWord ++ tailWord_17044) baseStart_17044 baseEnd_17044 := by
    simpa [prefixWord, tailWord_17044, baseEnd_17044] using wordTrace_append hprefix tailTrace_17044
  have hstable : (prefixWord ++ tailWord_17044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17044).length < 2 ^ (prefixWord ++ tailWord_17044).sum := by decide
  have hdescent : baseEnd_17044 < baseStart_17044 := by decide
  rcases family_descends (prefixWord ++ tailWord_17044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17049 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 4, 2]
def baseStart_17049 : Nat := 118140960795 + 17049 * 2 ^ 59
def prefixEnd_17049 : Nat := 4983230072969 + 3 ^ 40 * 17049 * 2
def baseEnd_17049 : Nat := 8754331678609029409099

theorem tailTrace_17049 : CollatzResearch.WordTrace tailWord_17049 prefixEnd_17049 8754331678609029409099 := by
  unfold tailWord_17049
  simp only [CollatzResearch.WordTrace]
  refine ⟨621828115241859582494201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 414552076827906388329467 621828115241859582494201)
  ·
    refine ⟨466371086431394686870651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 621828115241859582494201 466371086431394686870651)
    ·
      refine ⟨699556629647092030305977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466371086431394686870651 699556629647092030305977)
      ·
        refine ⟨524667472235319022729483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699556629647092030305977 524667472235319022729483)
        ·
          refine ⟨787001208352978534094225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524667472235319022729483 787001208352978534094225)
          ·
            refine ⟨590250906264733900570669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787001208352978534094225 590250906264733900570669)
            ·
              refine ⟨221344089849275212714001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590250906264733900570669 221344089849275212714001)
              ·
                refine ⟨166008067386956409535501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221344089849275212714001 166008067386956409535501)
                ·
                  refine ⟨62253025270108653575813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166008067386956409535501 62253025270108653575813)
                  ·
                    refine ⟨11672442238145372545465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62253025270108653575813 11672442238145372545465)
                    ·
                      refine ⟨8754331678609029409099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11672442238145372545465 8754331678609029409099)
                      ·
                        rfl

theorem cell23_17049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_17049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17049 prefixEnd_17049 := by exact prefixLift 17049
  have htrace : WordTrace (prefixWord ++ tailWord_17049) baseStart_17049 baseEnd_17049 := by
    simpa [prefixWord, tailWord_17049, baseEnd_17049] using wordTrace_append hprefix tailTrace_17049
  have hstable : (prefixWord ++ tailWord_17049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17049).length < 2 ^ (prefixWord ++ tailWord_17049).sum := by decide
  have hdescent : baseEnd_17049 < baseStart_17049 := by decide
  rcases family_descends (prefixWord ++ tailWord_17049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17094 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_17094 : Nat := 118140960795 + 17094 * 2 ^ 59
def prefixEnd_17094 : Nat := 4983230072969 + 3 ^ 40 * 17094 * 2
def baseEnd_17094 : Nat := 8777438308061353346393

theorem tailTrace_17094 : CollatzResearch.WordTrace tailWord_17094 prefixEnd_17094 8777438308061353346393 := by
  unfold tailWord_17094
  simp only [CollatzResearch.WordTrace]
  refine ⟨19483418752463508371323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 415646266719221511921557 19483418752463508371323)
  ·
    refine ⟨29225128128695262556985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19483418752463508371323 29225128128695262556985)
    ·
      refine ⟨21918846096521446917739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29225128128695262556985 21918846096521446917739)
      ·
        refine ⟨32878269144782170376609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21918846096521446917739 32878269144782170376609)
        ·
          refine ⟨24658701858586627782457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32878269144782170376609 24658701858586627782457)
          ·
            refine ⟨18494026393939970836843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24658701858586627782457 18494026393939970836843)
            ·
              refine ⟨27741039590909956255265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18494026393939970836843 27741039590909956255265)
              ·
                refine ⟨20805779693182467191449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27741039590909956255265 20805779693182467191449)
                ·
                  refine ⟨15604334769886850393587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20805779693182467191449 15604334769886850393587)
                  ·
                    refine ⟨23406502154830275590381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15604334769886850393587 23406502154830275590381)
                    ·
                      refine ⟨8777438308061353346393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 23406502154830275590381 8777438308061353346393)
                      ·
                        rfl

theorem cell23_17094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_17094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17094 prefixEnd_17094 := by exact prefixLift 17094
  have htrace : WordTrace (prefixWord ++ tailWord_17094) baseStart_17094 baseEnd_17094 := by
    simpa [prefixWord, tailWord_17094, baseEnd_17094] using wordTrace_append hprefix tailTrace_17094
  have hstable : (prefixWord ++ tailWord_17094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17094).length < 2 ^ (prefixWord ++ tailWord_17094).sum := by decide
  have hdescent : baseEnd_17094 < baseStart_17094 := by decide
  rcases family_descends (prefixWord ++ tailWord_17094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17100 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_17100 : Nat := 118140960795 + 17100 * 2 ^ 59
def prefixEnd_17100 : Nat := 4983230072969 + 3 ^ 40 * 17100 * 2
def baseEnd_17100 : Nat := 8780519191988329871365

theorem tailTrace_17100 : CollatzResearch.WordTrace tailWord_17100 prefixEnd_17100 8780519191988329871365 := by
  unfold tailWord_17100
  simp only [CollatzResearch.WordTrace]
  refine ⟨311844119028547646300377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 415792158704730195067169 311844119028547646300377)
  ·
    refine ⟨233883089271410734725283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311844119028547646300377 233883089271410734725283)
    ·
      refine ⟨350824633907116102087925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233883089271410734725283 350824633907116102087925)
      ·
        refine ⟨32889809428792134570743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 350824633907116102087925 32889809428792134570743)
        ·
          refine ⟨49334714143188201856115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32889809428792134570743 49334714143188201856115)
          ·
            refine ⟨74002071214782302784173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49334714143188201856115 74002071214782302784173)
            ·
              refine ⟨27750776705543363544065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74002071214782302784173 27750776705543363544065)
              ·
                refine ⟨20813082529157522658049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27750776705543363544065 20813082529157522658049)
                ·
                  refine ⟨15609811896868141993537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20813082529157522658049 15609811896868141993537)
                  ·
                    refine ⟨11707358922651106495153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15609811896868141993537 11707358922651106495153)
                    ·
                      refine ⟨8780519191988329871365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11707358922651106495153 8780519191988329871365)
                      ·
                        rfl

theorem cell23_17100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_17100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17100 prefixEnd_17100 := by exact prefixLift 17100
  have htrace : WordTrace (prefixWord ++ tailWord_17100) baseStart_17100 baseEnd_17100 := by
    simpa [prefixWord, tailWord_17100, baseEnd_17100] using wordTrace_append hprefix tailTrace_17100
  have hstable : (prefixWord ++ tailWord_17100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17100).length < 2 ^ (prefixWord ++ tailWord_17100).sum := by decide
  have hdescent : baseEnd_17100 < baseStart_17100 := by decide
  rcases family_descends (prefixWord ++ tailWord_17100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17106 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 7]
def baseStart_17106 : Nat := 118140960795 + 17106 * 2 ^ 59
def prefixEnd_17106 : Nat := 4983230072969 + 3 ^ 40 * 17106 * 2
def baseEnd_17106 : Nat := 975955563990589599593

theorem tailTrace_17106 : CollatzResearch.WordTrace tailWord_17106 prefixEnd_17106 975955563990589599593 := by
  unfold tailWord_17106
  simp only [CollatzResearch.WordTrace]
  refine ⟨155976769008839579329793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 415938050690238878212781 155976769008839579329793)
  ·
    refine ⟨116982576756629684497345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 155976769008839579329793 116982576756629684497345)
    ·
      refine ⟨87736932567472263373009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116982576756629684497345 87736932567472263373009)
      ·
        refine ⟨65802699425604197529757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87736932567472263373009 65802699425604197529757)
        ·
          refine ⟨24676012284601574073659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65802699425604197529757 24676012284601574073659)
          ·
            refine ⟨37014018426902361110489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24676012284601574073659 37014018426902361110489)
            ·
              refine ⟨27760513820176770832867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37014018426902361110489 27760513820176770832867)
              ·
                refine ⟨41640770730265156249301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27760513820176770832867 41640770730265156249301)
                ·
                  refine ⟨975955563990589599593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41640770730265156249301 975955563990589599593)
                  ·
                    rfl

theorem cell23_17106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_17106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17106 prefixEnd_17106 := by exact prefixLift 17106
  have htrace : WordTrace (prefixWord ++ tailWord_17106) baseStart_17106 baseEnd_17106 := by
    simpa [prefixWord, tailWord_17106, baseEnd_17106] using wordTrace_append hprefix tailTrace_17106
  have hstable : (prefixWord ++ tailWord_17106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17106).length < 2 ^ (prefixWord ++ tailWord_17106).sum := by decide
  have hdescent : baseEnd_17106 < baseStart_17106 := by decide
  rcases family_descends (prefixWord ++ tailWord_17106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17132 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_17132 : Nat := 118140960795 + 17132 * 2 ^ 59
def prefixEnd_17132 : Nat := 4983230072969 + 3 ^ 40 * 17132 * 2
def baseEnd_17132 : Nat := 2932316857644068223739

theorem tailTrace_17132 : CollatzResearch.WordTrace tailWord_17132 prefixEnd_17132 2932316857644068223739 := by
  unfold tailWord_17132
  simp only [CollatzResearch.WordTrace]
  refine ⟨312427686970582378882825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 416570249294109838510433 312427686970582378882825)
  ·
    refine ⟨234320765227936784162119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 312427686970582378882825 234320765227936784162119)
    ·
      refine ⟨351481147841905176243179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234320765227936784162119 351481147841905176243179)
      ·
        refine ⟨527221721762857764364769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351481147841905176243179 527221721762857764364769)
        ·
          refine ⟨395416291322143323273577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527221721762857764364769 395416291322143323273577)
          ·
            refine ⟨296562218491607492455183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395416291322143323273577 296562218491607492455183)
            ·
              refine ⟨444843327737411238682775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296562218491607492455183 444843327737411238682775)
              ·
                refine ⟨667264991606116858024163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444843327737411238682775 667264991606116858024163)
                ·
                  refine ⟨1000897487409175287036245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667264991606116858024163 1000897487409175287036245)
                  ·
                    refine ⟨2932316857644068223739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1000897487409175287036245 2932316857644068223739)
                    ·
                      rfl

theorem cell23_17132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_17132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17132 prefixEnd_17132 := by exact prefixLift 17132
  have htrace : WordTrace (prefixWord ++ tailWord_17132) baseStart_17132 baseEnd_17132 := by
    simpa [prefixWord, tailWord_17132, baseEnd_17132] using wordTrace_append hprefix tailTrace_17132
  have hstable : (prefixWord ++ tailWord_17132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17132).length < 2 ^ (prefixWord ++ tailWord_17132).sum := by decide
  have hdescent : baseEnd_17132 < baseStart_17132 := by decide
  rcases family_descends (prefixWord ++ tailWord_17132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17139 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4]
def baseStart_17139 : Nat := 118140960795 + 17139 * 2 ^ 59
def prefixEnd_17139 : Nat := 4983230072969 + 3 ^ 40 * 17139 * 2
def baseEnd_17139 : Nat := 8800544937513677283685

theorem tailTrace_17139 : CollatzResearch.WordTrace tailWord_17139 prefixEnd_17139 8800544937513677283685 := by
  unfold tailWord_17139
  simp only [CollatzResearch.WordTrace]
  refine ⟨625110684915804953270471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 416740456610536635513647 625110684915804953270471)
  ·
    refine ⟨937666027373707429905707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 625110684915804953270471 937666027373707429905707)
    ·
      refine ⟨1406499041060561144858561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937666027373707429905707 1406499041060561144858561)
      ·
        refine ⟨1054874280795420858643921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1406499041060561144858561 1054874280795420858643921)
        ·
          refine ⟨791155710596565643982941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054874280795420858643921 791155710596565643982941)
          ·
            refine ⟨296683391473712116493603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 791155710596565643982941 296683391473712116493603)
            ·
              refine ⟨445025087210568174740405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296683391473712116493603 445025087210568174740405)
              ·
                refine ⟨41721101925990766381913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445025087210568174740405 41721101925990766381913)
                ·
                  refine ⟨31290826444493074786435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41721101925990766381913 31290826444493074786435)
                  ·
                    refine ⟨46936239666739612179653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31290826444493074786435 46936239666739612179653)
                    ·
                      refine ⟨8800544937513677283685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 46936239666739612179653 8800544937513677283685)
                      ·
                        rfl

theorem cell23_17139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_17139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17139 prefixEnd_17139 := by exact prefixLift 17139
  have htrace : WordTrace (prefixWord ++ tailWord_17139) baseStart_17139 baseEnd_17139 := by
    simpa [prefixWord, tailWord_17139, baseEnd_17139] using wordTrace_append hprefix tailTrace_17139
  have hstable : (prefixWord ++ tailWord_17139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17139).length < 2 ^ (prefixWord ++ tailWord_17139).sum := by decide
  have hdescent : baseEnd_17139 < baseStart_17139 := by decide
  rcases family_descends (prefixWord ++ tailWord_17139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17156 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_17156 : Nat := 118140960795 + 17156 * 2 ^ 59
def prefixEnd_17156 : Nat := 4983230072969 + 3 ^ 40 * 17156 * 2
def baseEnd_17156 : Nat := 8809274108640110771107

theorem tailTrace_17156 : CollatzResearch.WordTrace tailWord_17156 prefixEnd_17156 8809274108640110771107 := by
  unfold tailWord_17156
  simp only [CollatzResearch.WordTrace]
  refine ⟨312865362927108428319661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 417153817236144571092881 312865362927108428319661)
  ·
    refine ⟨117324511097665660619873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 312865362927108428319661 117324511097665660619873)
    ·
      refine ⟨87993383323249245464905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117324511097665660619873 87993383323249245464905)
      ·
        refine ⟨65995037492436934098679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87993383323249245464905 65995037492436934098679)
        ·
          refine ⟨98992556238655401148019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65995037492436934098679 98992556238655401148019)
          ·
            refine ⟨148488834357983101722029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98992556238655401148019 148488834357983101722029)
            ·
              refine ⟨55683312884243663145761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148488834357983101722029 55683312884243663145761)
              ·
                refine ⟨41762484663182747359321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55683312884243663145761 41762484663182747359321)
                ·
                  refine ⟨31321863497387060519491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41762484663182747359321 31321863497387060519491)
                  ·
                    refine ⟨46982795246080590779237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31321863497387060519491 46982795246080590779237)
                    ·
                      refine ⟨8809274108640110771107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 46982795246080590779237 8809274108640110771107)
                      ·
                        rfl

theorem cell23_17156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_17156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17156 prefixEnd_17156 := by exact prefixLift 17156
  have htrace : WordTrace (prefixWord ++ tailWord_17156) baseStart_17156 baseEnd_17156 := by
    simpa [prefixWord, tailWord_17156, baseEnd_17156] using wordTrace_append hprefix tailTrace_17156
  have hstable : (prefixWord ++ tailWord_17156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17156).length < 2 ^ (prefixWord ++ tailWord_17156).sum := by decide
  have hdescent : baseEnd_17156 < baseStart_17156 := by decide
  rcases family_descends (prefixWord ++ tailWord_17156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17213 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 6]
def baseStart_17213 : Nat := 118140960795 + 17213 * 2 ^ 59
def prefixEnd_17213 : Nat := 4983230072969 + 3 ^ 40 * 17213 * 2
def baseEnd_17213 : Nat := 982060278438487528705

theorem tailTrace_17213 : CollatzResearch.WordTrace tailWord_17213 prefixEnd_17213 982060278438487528705 := by
  unfold tailWord_17213
  simp only [CollatzResearch.WordTrace]
  refine ⟨627809686647715591464293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 418539791098477060976195 627809686647715591464293)
  ·
    refine ⟨117714316246446673399555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 627809686647715591464293 117714316246446673399555)
    ·
      refine ⟨176571474369670010099333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117714316246446673399555 176571474369670010099333)
      ·
        refine ⟨33107151444313126893625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176571474369670010099333 33107151444313126893625)
        ·
          refine ⟨24830363583234845170219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33107151444313126893625 24830363583234845170219)
          ·
            refine ⟨37245545374852267755329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24830363583234845170219 37245545374852267755329)
            ·
              refine ⟨27934159031139200816497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37245545374852267755329 27934159031139200816497)
              ·
                refine ⟨20950619273354400612373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27934159031139200816497 20950619273354400612373)
                ·
                  refine ⟨982060278438487528705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20950619273354400612373 982060278438487528705)
                  ·
                    rfl

theorem cell23_17213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_17213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17213 prefixEnd_17213 := by exact prefixLift 17213
  have htrace : WordTrace (prefixWord ++ tailWord_17213) baseStart_17213 baseEnd_17213 := by
    simpa [prefixWord, tailWord_17213, baseEnd_17213] using wordTrace_append hprefix tailTrace_17213
  have hstable : (prefixWord ++ tailWord_17213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17213).length < 2 ^ (prefixWord ++ tailWord_17213).sum := by decide
  have hdescent : baseEnd_17213 < baseStart_17213 := by decide
  rcases family_descends (prefixWord ++ tailWord_17213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17217 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 1, 4]
def baseStart_17217 : Nat := 118140960795 + 17217 * 2 ^ 59
def prefixEnd_17217 : Nat := 4983230072969 + 3 ^ 40 * 17217 * 2
def baseEnd_17217 : Nat := 2946865476188124036109

theorem tailTrace_17217 : CollatzResearch.WordTrace tailWord_17217 prefixEnd_17217 2946865476188124036109 := by
  unfold tailWord_17217
  simp only [CollatzResearch.WordTrace]
  refine ⟨627955578633224274609905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 418637052422149516406603 627955578633224274609905)
  ·
    refine ⟨470966683974918205957429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 627955578633224274609905 470966683974918205957429)
    ·
      refine ⟨44153126622648581808509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 470966683974918205957429 44153126622648581808509)
      ·
        refine ⟨16557422483493218178191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44153126622648581808509 16557422483493218178191)
        ·
          refine ⟨24836133725239827267287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16557422483493218178191 24836133725239827267287)
          ·
            refine ⟨37254200587859740900931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24836133725239827267287 37254200587859740900931)
            ·
              refine ⟨55881300881789611351397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37254200587859740900931 55881300881789611351397)
              ·
                refine ⟨10477743915335552128387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55881300881789611351397 10477743915335552128387)
                ·
                  refine ⟨15716615873003328192581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477743915335552128387 15716615873003328192581)
                  ·
                    refine ⟨2946865476188124036109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15716615873003328192581 2946865476188124036109)
                    ·
                      rfl

theorem cell23_17217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_17217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17217 prefixEnd_17217 := by exact prefixLift 17217
  have htrace : WordTrace (prefixWord ++ tailWord_17217) baseStart_17217 baseEnd_17217 := by
    simpa [prefixWord, tailWord_17217, baseEnd_17217] using wordTrace_append hprefix tailTrace_17217
  have hstable : (prefixWord ++ tailWord_17217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17217).length < 2 ^ (prefixWord ++ tailWord_17217).sum := by decide
  have hdescent : baseEnd_17217 < baseStart_17217 := by decide
  rcases family_descends (prefixWord ++ tailWord_17217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17249 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_17249 : Nat := 118140960795 + 17249 * 2 ^ 59
def prefixEnd_17249 : Nat := 4983230072969 + 3 ^ 40 * 17249 * 2
def baseEnd_17249 : Nat := 8857027809508246908179

theorem tailTrace_17249 : CollatzResearch.WordTrace tailWord_17249 prefixEnd_17249 8857027809508246908179 := by
  unfold tailWord_17249
  simp only [CollatzResearch.WordTrace]
  refine ⟨629122714517293739774801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 419415143011529159849867 629122714517293739774801)
  ·
    refine ⟨471842035887970304831101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629122714517293739774801 471842035887970304831101)
    ·
      refine ⟨176940763457988864311663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 471842035887970304831101 176940763457988864311663)
      ·
        refine ⟨265411145186983296467495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176940763457988864311663 265411145186983296467495)
        ·
          refine ⟨398116717780474944701243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265411145186983296467495 398116717780474944701243)
          ·
            refine ⟨597175076670712417051865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398116717780474944701243 597175076670712417051865)
            ·
              refine ⟨447881307503034312788899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597175076670712417051865 447881307503034312788899)
              ·
                refine ⟨671821961254551469183349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447881307503034312788899 671821961254551469183349)
                ·
                  refine ⟨62983308867614200235939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671821961254551469183349 62983308867614200235939)
                  ·
                    refine ⟨94474963301421300353909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62983308867614200235939 94474963301421300353909)
                    ·
                      refine ⟨8857027809508246908179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 94474963301421300353909 8857027809508246908179)
                      ·
                        rfl

theorem cell23_17249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_17249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17249 prefixEnd_17249 := by exact prefixLift 17249
  have htrace : WordTrace (prefixWord ++ tailWord_17249) baseStart_17249 baseEnd_17249 := by
    simpa [prefixWord, tailWord_17249, baseEnd_17249] using wordTrace_append hprefix tailTrace_17249
  have hstable : (prefixWord ++ tailWord_17249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17249).length < 2 ^ (prefixWord ++ tailWord_17249).sum := by decide
  have hdescent : baseEnd_17249 < baseStart_17249 := by decide
  rcases family_descends (prefixWord ++ tailWord_17249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17250 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_17250 : Nat := 118140960795 + 17250 * 2 ^ 59
def prefixEnd_17250 : Nat := 4983230072969 + 3 ^ 40 * 17250 * 2
def baseEnd_17250 : Nat := 8857541290162742995675

theorem tailTrace_17250 : CollatzResearch.WordTrace tailWord_17250 prefixEnd_17250 8857541290162742995675 := by
  unfold tailWord_17250
  simp only [CollatzResearch.WordTrace]
  refine ⟨157289796878417727640301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 419439458342447273707469 157289796878417727640301)
  ·
    refine ⟨58983673829406647865113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157289796878417727640301 58983673829406647865113)
    ·
      refine ⟨44237755372054985898835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58983673829406647865113 44237755372054985898835)
      ·
        refine ⟨66356633058082478848253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44237755372054985898835 66356633058082478848253)
        ·
          refine ⟨24883737396780929568095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66356633058082478848253 24883737396780929568095)
          ·
            refine ⟨37325606095171394352143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24883737396780929568095 37325606095171394352143)
            ·
              refine ⟨55988409142757091528215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37325606095171394352143 55988409142757091528215)
              ·
                refine ⟨83982613714135637292323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55988409142757091528215 83982613714135637292323)
                ·
                  refine ⟨125973920571203455938485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83982613714135637292323 125973920571203455938485)
                  ·
                    refine ⟨11810055053550323994233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125973920571203455938485 11810055053550323994233)
                    ·
                      refine ⟨8857541290162742995675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11810055053550323994233 8857541290162742995675)
                      ·
                        rfl

theorem cell23_17250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_17250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17250 prefixEnd_17250 := by exact prefixLift 17250
  have htrace : WordTrace (prefixWord ++ tailWord_17250) baseStart_17250 baseEnd_17250 := by
    simpa [prefixWord, tailWord_17250, baseEnd_17250] using wordTrace_append hprefix tailTrace_17250
  have hstable : (prefixWord ++ tailWord_17250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17250).length < 2 ^ (prefixWord ++ tailWord_17250).sum := by decide
  have hdescent : baseEnd_17250 < baseStart_17250 := by decide
  rcases family_descends (prefixWord ++ tailWord_17250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17256 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_17256 : Nat := 118140960795 + 17256 * 2 ^ 59
def prefixEnd_17256 : Nat := 4983230072969 + 3 ^ 40 * 17256 * 2
def baseEnd_17256 : Nat := 2953540724696573173549

theorem tailTrace_17256 : CollatzResearch.WordTrace tailWord_17256 prefixEnd_17256 2953540724696573173549 := by
  unfold tailWord_17256
  simp only [CollatzResearch.WordTrace]
  refine ⟨314689012745966967639811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 419585350327955956853081 314689012745966967639811)
  ·
    refine ⟨472033519118950451459717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 314689012745966967639811 472033519118950451459717)
    ·
      refine ⟨88506284834803209648697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 472033519118950451459717 88506284834803209648697)
      ·
        refine ⟨66379713626102407236523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88506284834803209648697 66379713626102407236523)
        ·
          refine ⟨99569570439153610854785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66379713626102407236523 99569570439153610854785)
          ·
            refine ⟨74677177829365208141089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99569570439153610854785 74677177829365208141089)
            ·
              refine ⟨56007883372023906105817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74677177829365208141089 56007883372023906105817)
              ·
                refine ⟨42005912529017929579363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56007883372023906105817 42005912529017929579363)
                ·
                  refine ⟨63008868793526894369045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42005912529017929579363 63008868793526894369045)
                  ·
                    refine ⟨2953540724696573173549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63008868793526894369045 2953540724696573173549)
                    ·
                      rfl

theorem cell23_17256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_17256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17256 prefixEnd_17256 := by exact prefixLift 17256
  have htrace : WordTrace (prefixWord ++ tailWord_17256) baseStart_17256 baseEnd_17256 := by
    simpa [prefixWord, tailWord_17256, baseEnd_17256] using wordTrace_append hprefix tailTrace_17256
  have hstable : (prefixWord ++ tailWord_17256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17256).length < 2 ^ (prefixWord ++ tailWord_17256).sum := by decide
  have hdescent : baseEnd_17256 < baseStart_17256 := by decide
  rcases family_descends (prefixWord ++ tailWord_17256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17273 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 2, 4]
def baseStart_17273 : Nat := 118140960795 + 17273 * 2 ^ 59
def prefixEnd_17273 : Nat := 4983230072969 + 3 ^ 40 * 17273 * 2
def baseEnd_17273 : Nat := 2956450448405384336023

theorem tailTrace_17273 : CollatzResearch.WordTrace tailWord_17273 prefixEnd_17273 2956450448405384336023 := by
  unfold tailWord_17273
  simp only [CollatzResearch.WordTrace]
  refine ⟨629998066430345838648473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 419998710953563892432315 629998066430345838648473)
  ·
    refine ⟨472498549822759378986355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629998066430345838648473 472498549822759378986355)
    ·
      refine ⟨708747824734139068479533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472498549822759378986355 708747824734139068479533)
      ·
        refine ⟨265780434275302150679825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 708747824734139068479533 265780434275302150679825)
        ·
          refine ⟨199335325706476613009869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265780434275302150679825 199335325706476613009869)
          ·
            refine ⟨74750747139928729878701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199335325706476613009869 74750747139928729878701)
            ·
              refine ⟨28031530177473273704513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74750747139928729878701 28031530177473273704513)
              ·
                refine ⟨21023647633104955278385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28031530177473273704513 21023647633104955278385)
                ·
                  refine ⟨15767735724828716458789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21023647633104955278385 15767735724828716458789)
                  ·
                    refine ⟨2956450448405384336023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15767735724828716458789 2956450448405384336023)
                    ·
                      rfl

theorem cell23_17273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 4].length) (baseStart_17273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17273 prefixEnd_17273 := by exact prefixLift 17273
  have htrace : WordTrace (prefixWord ++ tailWord_17273) baseStart_17273 baseEnd_17273 := by
    simpa [prefixWord, tailWord_17273, baseEnd_17273] using wordTrace_append hprefix tailTrace_17273
  have hstable : (prefixWord ++ tailWord_17273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17273).length < 2 ^ (prefixWord ++ tailWord_17273).sum := by decide
  have hdescent : baseEnd_17273 < baseStart_17273 := by decide
  rcases family_descends (prefixWord ++ tailWord_17273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17300 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_17300 : Nat := 118140960795 + 17300 * 2 ^ 59
def prefixEnd_17300 : Nat := 4983230072969 + 3 ^ 40 * 17300 * 2
def baseEnd_17300 : Nat := 8883215322887547370445

theorem tailTrace_17300 : CollatzResearch.WordTrace tailWord_17300 prefixEnd_17300 8883215322887547370445 := by
  unfold tailWord_17300
  simp only [CollatzResearch.WordTrace]
  refine ⟨315491418666264724940677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 420655224888352966587569 315491418666264724940677)
  ·
    refine ⟨59154640999924635926377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 315491418666264724940677 59154640999924635926377)
    ·
      refine ⟨44365980749943476944783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59154640999924635926377 44365980749943476944783)
      ·
        refine ⟨66548971124915215417175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44365980749943476944783 66548971124915215417175)
        ·
          refine ⟨99823456687372823125763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66548971124915215417175 99823456687372823125763)
          ·
            refine ⟨149735185031059234688645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99823456687372823125763 149735185031059234688645)
            ·
              refine ⟨28075347193323606504121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149735185031059234688645 28075347193323606504121)
              ·
                refine ⟨21056510394992704878091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28075347193323606504121 21056510394992704878091)
                ·
                  refine ⟨31584765592489057317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21056510394992704878091 31584765592489057317137)
                  ·
                    refine ⟨23688574194366792987853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31584765592489057317137 23688574194366792987853)
                    ·
                      refine ⟨8883215322887547370445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 23688574194366792987853 8883215322887547370445)
                      ·
                        rfl

theorem cell23_17300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_17300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17300 prefixEnd_17300 := by exact prefixLift 17300
  have htrace : WordTrace (prefixWord ++ tailWord_17300) baseStart_17300 baseEnd_17300 := by
    simpa [prefixWord, tailWord_17300, baseEnd_17300] using wordTrace_append hprefix tailTrace_17300
  have hstable : (prefixWord ++ tailWord_17300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17300).length < 2 ^ (prefixWord ++ tailWord_17300).sum := by decide
  have hdescent : baseEnd_17300 < baseStart_17300 := by decide
  rcases family_descends (prefixWord ++ tailWord_17300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17314 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_17314 : Nat := 118140960795 + 17314 * 2 ^ 59
def prefixEnd_17314 : Nat := 4983230072969 + 3 ^ 40 * 17314 * 2
def baseEnd_17314 : Nat := 8890404052050492595381

theorem tailTrace_17314 : CollatzResearch.WordTrace tailWord_17314 prefixEnd_17314 8890404052050492595381 := by
  unfold tailWord_17314
  simp only [CollatzResearch.WordTrace]
  refine ⟨157873364820452460222749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 420995639521206560593997 157873364820452460222749)
  ·
    refine ⟨59202511807669672583531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157873364820452460222749 59202511807669672583531)
    ·
      refine ⟨88803767711504508875297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59202511807669672583531 88803767711504508875297)
      ·
        refine ⟨66602825783628381656473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88803767711504508875297 66602825783628381656473)
        ·
          refine ⟨49952119337721286242355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66602825783628381656473 49952119337721286242355)
          ·
            refine ⟨74928179006581929363533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49952119337721286242355 74928179006581929363533)
            ·
              refine ⟨28098067127468223511325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74928179006581929363533 28098067127468223511325)
              ·
                refine ⟨10536775172800583816747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28098067127468223511325 10536775172800583816747)
                ·
                  refine ⟨15805162759200875725121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10536775172800583816747 15805162759200875725121)
                  ·
                    refine ⟨11853872069400656793841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15805162759200875725121 11853872069400656793841)
                    ·
                      refine ⟨8890404052050492595381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 11853872069400656793841 8890404052050492595381)
                      ·
                        rfl

theorem cell23_17314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_17314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17314 prefixEnd_17314 := by exact prefixLift 17314
  have htrace : WordTrace (prefixWord ++ tailWord_17314) baseStart_17314 baseEnd_17314 := by
    simpa [prefixWord, tailWord_17314, baseEnd_17314] using wordTrace_append hprefix tailTrace_17314
  have hstable : (prefixWord ++ tailWord_17314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17314).length < 2 ^ (prefixWord ++ tailWord_17314).sum := by decide
  have hdescent : baseEnd_17314 < baseStart_17314 := by decide
  rcases family_descends (prefixWord ++ tailWord_17314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17356 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_17356 : Nat := 118140960795 + 17356 * 2 ^ 59
def prefixEnd_17356 : Nat := 4983230072969 + 3 ^ 40 * 17356 * 2
def baseEnd_17356 : Nat := 8911970239539328270187

theorem tailTrace_17356 : CollatzResearch.WordTrace tailWord_17356 prefixEnd_17356 8911970239539328270187 := by
  unfold tailWord_17356
  simp only [CollatzResearch.WordTrace]
  refine ⟨316512662564825506959961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 422016883419767342613281 316512662564825506959961)
  ·
    refine ⟨237384496923619130219971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 316512662564825506959961 237384496923619130219971)
    ·
      refine ⟨356076745385428695329957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237384496923619130219971 356076745385428695329957)
      ·
        refine ⟨66764389759767880374367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 356076745385428695329957 66764389759767880374367)
        ·
          refine ⟨100146584639651820561551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66764389759767880374367 100146584639651820561551)
          ·
            refine ⟨150219876959477730842327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100146584639651820561551 150219876959477730842327)
            ·
              refine ⟨225329815439216596263491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150219876959477730842327 225329815439216596263491)
              ·
                refine ⟨337994723158824894395237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225329815439216596263491 337994723158824894395237)
                ·
                  refine ⟨63374010592279667699107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337994723158824894395237 63374010592279667699107)
                  ·
                    refine ⟨95061015888419501548661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63374010592279667699107 95061015888419501548661)
                    ·
                      refine ⟨8911970239539328270187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 95061015888419501548661 8911970239539328270187)
                      ·
                        rfl

theorem cell23_17356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_17356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_17356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_17356 prefixEnd_17356 := by exact prefixLift 17356
  have htrace : WordTrace (prefixWord ++ tailWord_17356) baseStart_17356 baseEnd_17356 := by
    simpa [prefixWord, tailWord_17356, baseEnd_17356] using wordTrace_append hprefix tailTrace_17356
  have hstable : (prefixWord ++ tailWord_17356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17356).length < 2 ^ (prefixWord ++ tailWord_17356).sum := by decide
  have hdescent : baseEnd_17356 < baseStart_17356 := by decide
  rcases family_descends (prefixWord ++ tailWord_17356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
