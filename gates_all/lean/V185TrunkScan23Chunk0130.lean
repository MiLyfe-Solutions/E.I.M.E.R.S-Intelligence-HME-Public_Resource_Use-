import V185TrunkScan23Chunk0129

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_769756 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_769756 : Nat := 118140960795 + 769756 * 2 ^ 59
def prefixEnd_769756 : Nat := 4983230072969 + 3 ^ 40 * 769756 * 2
def baseEnd_769756 : Nat := 395254814682395559809963

theorem tailTrace_769756 : CollatzResearch.WordTrace tailWord_769756 prefixEnd_769756 395254814682395559809963 := by
  unfold tailWord_769756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14037653899656475351768561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18716871866208633802358081 14037653899656475351768561)
  ·
    refine ⟨10528240424742356513826421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14037653899656475351768561 10528240424742356513826421)
    ·
      refine ⟨987022539819595923171227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10528240424742356513826421 987022539819595923171227)
      ·
        refine ⟨1480533809729393884756841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987022539819595923171227 1480533809729393884756841)
        ·
          refine ⟨1110400357297045413567631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480533809729393884756841 1110400357297045413567631)
          ·
            refine ⟨1665600535945568120351447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110400357297045413567631 1665600535945568120351447)
            ·
              refine ⟨2498400803918352180527171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665600535945568120351447 2498400803918352180527171)
              ·
                refine ⟨3747601205877528270790757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498400803918352180527171 3747601205877528270790757)
                ·
                  refine ⟨702675226102036550773267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3747601205877528270790757 702675226102036550773267)
                  ·
                    refine ⟨1054012839153054826159901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 702675226102036550773267 1054012839153054826159901)
                    ·
                      refine ⟨395254814682395559809963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054012839153054826159901 395254814682395559809963)
                      ·
                        rfl

theorem cell23_769756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_769756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769756 prefixEnd_769756 := by exact prefixLift 769756
  have htrace : WordTrace (prefixWord ++ tailWord_769756) baseStart_769756 baseEnd_769756 := by
    simpa [prefixWord, tailWord_769756, baseEnd_769756] using wordTrace_append hprefix tailTrace_769756
  have hstable : (prefixWord ++ tailWord_769756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769756).length < 2 ^ (prefixWord ++ tailWord_769756).sum := by decide
  have hdescent : baseEnd_769756 < baseStart_769756 := by decide
  rcases family_descends (prefixWord ++ tailWord_769756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769775 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_769775 : Nat := 118140960795 + 769775 * 2 ^ 59
def prefixEnd_769775 : Nat := 4983230072969 + 3 ^ 40 * 769775 * 2
def baseEnd_769775 : Nat := 395264570814830985472375

theorem tailTrace_769775 : CollatzResearch.WordTrace tailWord_769775 prefixEnd_769775 395264570814830985472375 := by
  unfold tailWord_769775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076000786244116948478779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18717333857496077965652519 28076000786244116948478779)
  ·
    refine ⟨42114001179366175422718169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076000786244116948478779 42114001179366175422718169)
    ·
      refine ⟨31585500884524631567038627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42114001179366175422718169 31585500884524631567038627)
      ·
        refine ⟨47378251326786947350557941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31585500884524631567038627 47378251326786947350557941)
        ·
          refine ⟨4441711061886276314114807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47378251326786947350557941 4441711061886276314114807)
          ·
            refine ⟨6662566592829414471172211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441711061886276314114807 6662566592829414471172211)
            ·
              refine ⟨9993849889244121706758317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6662566592829414471172211 9993849889244121706758317)
              ·
                refine ⟨3747693708466545640034369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9993849889244121706758317 3747693708466545640034369)
                ·
                  refine ⟨2810770281349909230025777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747693708466545640034369 2810770281349909230025777)
                  ·
                    refine ⟨2108077711012431922519333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2810770281349909230025777 2108077711012431922519333)
                    ·
                      refine ⟨395264570814830985472375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2108077711012431922519333 395264570814830985472375)
                      ·
                        rfl

theorem cell23_769775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_769775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769775 prefixEnd_769775 := by exact prefixLift 769775
  have htrace : WordTrace (prefixWord ++ tailWord_769775) baseStart_769775 baseEnd_769775 := by
    simpa [prefixWord, tailWord_769775, baseEnd_769775] using wordTrace_append hprefix tailTrace_769775
  have hstable : (prefixWord ++ tailWord_769775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769775).length < 2 ^ (prefixWord ++ tailWord_769775).sum := by decide
  have hdescent : baseEnd_769775 < baseStart_769775 := by decide
  rcases family_descends (prefixWord ++ tailWord_769775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769779 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 2, 2, 2]
def baseStart_769779 : Nat := 118140960795 + 769779 * 2 ^ 59
def prefixEnd_769779 : Nat := 4983230072969 + 3 ^ 40 * 769779 * 2
def baseEnd_769779 : Nat := 395266624737448969822357

theorem tailTrace_769779 : CollatzResearch.WordTrace tailWord_769779 prefixEnd_769779 395266624737448969822357 := by
  unfold tailWord_769779
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076146678229625631624391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18717431118819750421082927 28076146678229625631624391)
  ·
    refine ⟨42114220017344438447436587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076146678229625631624391 42114220017344438447436587)
    ·
      refine ⟨63171330026016657671154881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42114220017344438447436587 63171330026016657671154881)
      ·
        refine ⟨47378497519512493253366161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63171330026016657671154881 47378497519512493253366161)
        ·
          refine ⟨35533873139634369940024621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47378497519512493253366161 35533873139634369940024621)
          ·
            refine ⟨13325202427362888727509233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35533873139634369940024621 13325202427362888727509233)
            ·
              refine ⟨9993901820522166545631925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13325202427362888727509233 9993901820522166545631925)
              ·
                refine ⟨936928295673953113652993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9993901820522166545631925 936928295673953113652993)
                ·
                  refine ⟨702696221755464835239745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 936928295673953113652993 702696221755464835239745)
                  ·
                    refine ⟨527022166316598626429809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 702696221755464835239745 527022166316598626429809)
                    ·
                      refine ⟨395266624737448969822357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527022166316598626429809 395266624737448969822357)
                      ·
                        rfl

theorem cell23_769779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 2, 2].length) (baseStart_769779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769779 prefixEnd_769779 := by exact prefixLift 769779
  have htrace : WordTrace (prefixWord ++ tailWord_769779) baseStart_769779 baseEnd_769779 := by
    simpa [prefixWord, tailWord_769779, baseEnd_769779] using wordTrace_append hprefix tailTrace_769779
  have hstable : (prefixWord ++ tailWord_769779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769779).length < 2 ^ (prefixWord ++ tailWord_769779).sum := by decide
  have hdescent : baseEnd_769779 < baseStart_769779 := by decide
  rcases family_descends (prefixWord ++ tailWord_769779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769795 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3]
def baseStart_769795 : Nat := 118140960795 + 769795 * 2 ^ 59
def prefixEnd_769795 : Nat := 4983230072969 + 3 ^ 40 * 769795 * 2
def baseEnd_769795 : Nat := 395274840427920907222283

theorem tailTrace_769795 : CollatzResearch.WordTrace tailWord_769795 prefixEnd_769795 395274840427920907222283 := by
  unfold tailWord_769795
  simp only [CollatzResearch.WordTrace]
  refine ⟨28076730246171660364206839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18717820164114440242804559 28076730246171660364206839)
  ·
    refine ⟨42115095369257490546310259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28076730246171660364206839 42115095369257490546310259)
    ·
      refine ⟨63172643053886235819465389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42115095369257490546310259 63172643053886235819465389)
      ·
        refine ⟨23689741145207338432299521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63172643053886235819465389 23689741145207338432299521)
        ·
          refine ⟨17767305858905503824224641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23689741145207338432299521 17767305858905503824224641)
          ·
            refine ⟨13325479394179127868168481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17767305858905503824224641 13325479394179127868168481)
            ·
              refine ⟨9994109545634345901126361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13325479394179127868168481 9994109545634345901126361)
              ·
                refine ⟨7495582159225759425844771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9994109545634345901126361 7495582159225759425844771)
                ·
                  refine ⟨11243373238838639138767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495582159225759425844771 11243373238838639138767157)
                  ·
                    refine ⟨1054066241141122419259421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11243373238838639138767157 1054066241141122419259421)
                    ·
                      refine ⟨395274840427920907222283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054066241141122419259421 395274840427920907222283)
                      ·
                        rfl

theorem cell23_769795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_769795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769795 prefixEnd_769795 := by exact prefixLift 769795
  have htrace : WordTrace (prefixWord ++ tailWord_769795) baseStart_769795 baseEnd_769795 := by
    simpa [prefixWord, tailWord_769795, baseEnd_769795] using wordTrace_append hprefix tailTrace_769795
  have hstable : (prefixWord ++ tailWord_769795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769795).length < 2 ^ (prefixWord ++ tailWord_769795).sum := by decide
  have hdescent : baseEnd_769795 < baseStart_769795 := by decide
  rcases family_descends (prefixWord ++ tailWord_769795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769825 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_769825 : Nat := 118140960795 + 769825 * 2 ^ 59
def prefixEnd_769825 : Nat := 4983230072969 + 3 ^ 40 * 769825 * 2
def baseEnd_769825 : Nat := 395290244847555789847145

theorem tailTrace_769825 : CollatzResearch.WordTrace tailWord_769825 prefixEnd_769825 395290244847555789847145 := by
  unfold tailWord_769825
  simp only [CollatzResearch.WordTrace]
  refine ⟨28077824436062975487798929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18718549624041983658532619 28077824436062975487798929)
  ·
    refine ⟨21058368327047231615849197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28077824436062975487798929 21058368327047231615849197)
    ·
      refine ⟨7896888122642711855943449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21058368327047231615849197 7896888122642711855943449)
      ·
        refine ⟨5922666091982033891957587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7896888122642711855943449 5922666091982033891957587)
        ·
          refine ⟨8883999137973050837936381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922666091982033891957587 8883999137973050837936381)
          ·
            refine ⟨3331499676739894064226143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8883999137973050837936381 3331499676739894064226143)
            ·
              refine ⟨4997249515109841096339215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331499676739894064226143 4997249515109841096339215)
              ·
                refine ⟨7495874272664761644508823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997249515109841096339215 7495874272664761644508823)
                ·
                  refine ⟨11243811408997142466763235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7495874272664761644508823 11243811408997142466763235)
                  ·
                    refine ⟨16865717113495713700144853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11243811408997142466763235 16865717113495713700144853)
                    ·
                      refine ⟨395290244847555789847145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16865717113495713700144853 395290244847555789847145)
                      ·
                        rfl

theorem cell23_769825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_769825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769825 prefixEnd_769825 := by exact prefixLift 769825
  have htrace : WordTrace (prefixWord ++ tailWord_769825) baseStart_769825 baseEnd_769825 := by
    simpa [prefixWord, tailWord_769825, baseEnd_769825] using wordTrace_append hprefix tailTrace_769825
  have hstable : (prefixWord ++ tailWord_769825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769825).length < 2 ^ (prefixWord ++ tailWord_769825).sum := by decide
  have hdescent : baseEnd_769825 < baseStart_769825 := by decide
  rcases family_descends (prefixWord ++ tailWord_769825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769852 : List Nat := [2, 2, 2, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_769852 : Nat := 118140960795 + 769852 * 2 ^ 59
def prefixEnd_769852 : Nat := 4983230072969 + 3 ^ 40 * 769852 * 2
def baseEnd_769852 : Nat := 395304108825227184209521

theorem tailTrace_769852 : CollatzResearch.WordTrace tailWord_769852 prefixEnd_769852 395304108825227184209521 := by
  unfold tailWord_769852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039404603482579549515905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18719206137976772732687873 14039404603482579549515905)
  ·
    refine ⟨10529553452611934662136929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14039404603482579549515905 10529553452611934662136929)
    ·
      refine ⟨7897165089458950996602697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10529553452611934662136929 7897165089458950996602697)
      ·
        refine ⟨5922873817094213247452023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7897165089458950996602697 5922873817094213247452023)
        ·
          refine ⟨8884310725641319871178035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5922873817094213247452023 8884310725641319871178035)
          ·
            refine ⟨13326466088461979806767053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884310725641319871178035 13326466088461979806767053)
            ·
              refine ⟨4997424783173242427537645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13326466088461979806767053 4997424783173242427537645)
              ·
                refine ⟨1874034293689965910326617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4997424783173242427537645 1874034293689965910326617)
                ·
                  refine ⟨1405525720267474432744963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1874034293689965910326617 1405525720267474432744963)
                  ·
                    refine ⟨2108288580401211649117445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1405525720267474432744963 2108288580401211649117445)
                    ·
                      refine ⟨395304108825227184209521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2108288580401211649117445 395304108825227184209521)
                      ·
                        rfl

theorem cell23_769852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_769852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769852 prefixEnd_769852 := by exact prefixLift 769852
  have htrace : WordTrace (prefixWord ++ tailWord_769852) baseStart_769852 baseEnd_769852 := by
    simpa [prefixWord, tailWord_769852, baseEnd_769852] using wordTrace_append hprefix tailTrace_769852
  have hstable : (prefixWord ++ tailWord_769852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769852).length < 2 ^ (prefixWord ++ tailWord_769852).sum := by decide
  have hdescent : baseEnd_769852 < baseStart_769852 := by decide
  rcases family_descends (prefixWord ++ tailWord_769852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769865 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_769865 : Nat := 118140960795 + 769865 * 2 ^ 59
def prefixEnd_769865 : Nat := 4983230072969 + 3 ^ 40 * 769865 * 2
def baseEnd_769865 : Nat := 395310784073735633346961

theorem tailTrace_769865 : CollatzResearch.WordTrace tailWord_769865 prefixEnd_769865 395310784073735633346961 := by
  unfold tailWord_769865
  simp only [CollatzResearch.WordTrace]
  refine ⟨28079283355918062319255049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18719522237278708212836699 28079283355918062319255049)
  ·
    refine ⟨21059462516938546739441287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28079283355918062319255049 21059462516938546739441287)
    ·
      refine ⟨31589193775407820109161931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21059462516938546739441287 31589193775407820109161931)
      ·
        refine ⟨47383790663111730163742897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31589193775407820109161931 47383790663111730163742897)
        ·
          refine ⟨35537842997333797622807173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47383790663111730163742897 35537842997333797622807173)
          ·
            refine ⟨6663345562000087054276345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35537842997333797622807173 6663345562000087054276345)
            ·
              refine ⟨4997509171500065290707259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6663345562000087054276345 4997509171500065290707259)
              ·
                refine ⟨7496263757250097936060889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997509171500065290707259 7496263757250097936060889)
                ·
                  refine ⟨5622197817937573452045667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496263757250097936060889 5622197817937573452045667)
                  ·
                    refine ⟨8433296726906360178068501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5622197817937573452045667 8433296726906360178068501)
                    ·
                      refine ⟨395310784073735633346961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8433296726906360178068501 395310784073735633346961)
                      ·
                        rfl

theorem cell23_769865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_769865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769865 prefixEnd_769865 := by exact prefixLift 769865
  have htrace : WordTrace (prefixWord ++ tailWord_769865) baseStart_769865 baseEnd_769865 := by
    simpa [prefixWord, tailWord_769865, baseEnd_769865] using wordTrace_append hprefix tailTrace_769865
  have hstable : (prefixWord ++ tailWord_769865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769865).length < 2 ^ (prefixWord ++ tailWord_769865).sum := by decide
  have hdescent : baseEnd_769865 < baseStart_769865 := by decide
  rcases family_descends (prefixWord ++ tailWord_769865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769915 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_769915 : Nat := 118140960795 + 769915 * 2 ^ 59
def prefixEnd_769915 : Nat := 4983230072969 + 3 ^ 40 * 769915 * 2
def baseEnd_769915 : Nat := 395336458106460437721731

theorem tailTrace_769915 : CollatzResearch.WordTrace tailWord_769915 prefixEnd_769915 395336458106460437721731 := by
  unfold tailWord_769915
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081107005736920858575199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18720738003824613905716799 28081107005736920858575199)
  ·
    refine ⟨42121660508605381287862799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28081107005736920858575199 42121660508605381287862799)
    ·
      refine ⟨63182490762908071931794199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42121660508605381287862799 63182490762908071931794199)
      ·
        refine ⟨94773736144362107897691299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63182490762908071931794199 94773736144362107897691299)
        ·
          refine ⟨142160604216543161846536949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94773736144362107897691299 142160604216543161846536949)
          ·
            refine ⟨13327556645300921423112839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142160604216543161846536949 13327556645300921423112839)
            ·
              refine ⟨19991334967951382134669259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13327556645300921423112839 19991334967951382134669259)
              ·
                refine ⟨29987002451927073202003889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19991334967951382134669259 29987002451927073202003889)
                ·
                  refine ⟨22490251838945304901502917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29987002451927073202003889 22490251838945304901502917)
                  ·
                    refine ⟨4216922219802244669031797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22490251838945304901502917 4216922219802244669031797)
                    ·
                      refine ⟨395336458106460437721731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4216922219802244669031797 395336458106460437721731)
                      ·
                        rfl

theorem cell23_769915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_769915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769915 prefixEnd_769915 := by exact prefixLift 769915
  have htrace : WordTrace (prefixWord ++ tailWord_769915) baseStart_769915 baseEnd_769915 := by
    simpa [prefixWord, tailWord_769915, baseEnd_769915] using wordTrace_append hprefix tailTrace_769915
  have hstable : (prefixWord ++ tailWord_769915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769915).length < 2 ^ (prefixWord ++ tailWord_769915).sum := by decide
  have hdescent : baseEnd_769915 < baseStart_769915 := by decide
  rcases family_descends (prefixWord ++ tailWord_769915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769929 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 4, 3, 2]
def baseStart_769929 : Nat := 118140960795 + 769929 * 2 ^ 59
def prefixEnd_769929 : Nat := 4983230072969 + 3 ^ 40 * 769929 * 2
def baseEnd_769929 : Nat := 395343646835623382946667

theorem tailTrace_769929 : CollatzResearch.WordTrace tailWord_769929 prefixEnd_769929 395343646835623382946667 := by
  unfold tailWord_769929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28081617627686201249584841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18721078418457467499723227 28081617627686201249584841)
  ·
    refine ⟨21061213220764650937188631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28081617627686201249584841 21061213220764650937188631)
    ·
      refine ⟨31591819831146976405782947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21061213220764650937188631 31591819831146976405782947)
      ·
        refine ⟨47387729746720464608674421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31591819831146976405782947 47387729746720464608674421)
        ·
          refine ⟨4442599663755043557063227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47387729746720464608674421 4442599663755043557063227)
          ·
            refine ⟨6663899495632565335594841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442599663755043557063227 6663899495632565335594841)
            ·
              refine ⟨4997924621724424001696131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6663899495632565335594841 4997924621724424001696131)
              ·
                refine ⟨7496886932586636002544197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997924621724424001696131 7496886932586636002544197)
                ·
                  refine ⟨1405666299859994250477037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7496886932586636002544197 1405666299859994250477037)
                  ·
                    refine ⟨527124862447497843928889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405666299859994250477037 527124862447497843928889)
                    ·
                      refine ⟨395343646835623382946667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527124862447497843928889 395343646835623382946667)
                      ·
                        rfl

theorem cell23_769929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 3, 2].length) (baseStart_769929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769929 prefixEnd_769929 := by exact prefixLift 769929
  have htrace : WordTrace (prefixWord ++ tailWord_769929) baseStart_769929 baseEnd_769929 := by
    simpa [prefixWord, tailWord_769929, baseEnd_769929] using wordTrace_append hprefix tailTrace_769929
  have hstable : (prefixWord ++ tailWord_769929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769929).length < 2 ^ (prefixWord ++ tailWord_769929).sum := by decide
  have hdescent : baseEnd_769929 < baseStart_769929 := by decide
  rcases family_descends (prefixWord ++ tailWord_769929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769969 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 4, 4]
def baseStart_769969 : Nat := 118140960795 + 769969 * 2 ^ 59
def prefixEnd_769969 : Nat := 4983230072969 + 3 ^ 40 * 769969 * 2
def baseEnd_769969 : Nat := 131788062020601075482161

theorem tailTrace_769969 : CollatzResearch.WordTrace tailWord_769969 prefixEnd_769969 131788062020601075482161 := by
  unfold tailWord_769969
  simp only [CollatzResearch.WordTrace]
  refine ⟨28083076547541288081040961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18722051031694192054027307 28083076547541288081040961)
  ·
    refine ⟨21062307410655966060780721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28083076547541288081040961 21062307410655966060780721)
    ·
      refine ⟨15796730557991974545585541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21062307410655966060780721 15796730557991974545585541)
      ·
        refine ⟨2961886979623495227297289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15796730557991974545585541 2961886979623495227297289)
        ·
          refine ⟨2221415234717621420472967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961886979623495227297289 2221415234717621420472967)
          ·
            refine ⟨3332122852076432130709451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221415234717621420472967 3332122852076432130709451)
            ·
              refine ⟨4998184278114648196064177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332122852076432130709451 4998184278114648196064177)
              ·
                refine ⟨3748638208585986147048133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998184278114648196064177 3748638208585986147048133)
                ·
                  refine ⟨702869664109872402571525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3748638208585986147048133 702869664109872402571525)
                  ·
                    refine ⟨131788062020601075482161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 702869664109872402571525 131788062020601075482161)
                    ·
                      rfl

theorem cell23_769969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_769969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769969 prefixEnd_769969 := by exact prefixLift 769969
  have htrace : WordTrace (prefixWord ++ tailWord_769969) baseStart_769969 baseEnd_769969 := by
    simpa [prefixWord, tailWord_769969, baseEnd_769969] using wordTrace_append hprefix tailTrace_769969
  have hstable : (prefixWord ++ tailWord_769969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769969).length < 2 ^ (prefixWord ++ tailWord_769969).sum := by decide
  have hdescent : baseEnd_769969 < baseStart_769969 := by decide
  rcases family_descends (prefixWord ++ tailWord_769969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_769982 : List Nat := [4, 2, 1, 1, 1, 3, 11]
def baseStart_769982 : Nat := 118140960795 + 769982 * 2 ^ 59
def prefixEnd_769982 : Nat := 4983230072969 + 3 ^ 40 * 769982 * 2
def baseEnd_769982 : Nat := 4881121744571749081283

theorem tailTrace_769982 : CollatzResearch.WordTrace tailWord_769982 prefixEnd_769982 4881121744571749081283 := by
  unfold tailWord_769982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3510443837061773912658025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18722367130996127534176133 3510443837061773912658025)
  ·
    refine ⟨2632832877796330434493519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3510443837061773912658025 2632832877796330434493519)
    ·
      refine ⟨3949249316694495651740279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2632832877796330434493519 3949249316694495651740279)
      ·
        refine ⟨5923873975041743477610419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949249316694495651740279 5923873975041743477610419)
        ·
          refine ⟨8885810962562615216415629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923873975041743477610419 8885810962562615216415629)
          ·
            refine ⟨3332179110960980706155861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8885810962562615216415629 3332179110960980706155861)
            ·
              refine ⟨4881121744571749081283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3332179110960980706155861 4881121744571749081283)
              ·
                rfl

theorem cell23_769982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 11].length) (baseStart_769982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_769982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_769982 prefixEnd_769982 := by exact prefixLift 769982
  have htrace : WordTrace (prefixWord ++ tailWord_769982) baseStart_769982 baseEnd_769982 := by
    simpa [prefixWord, tailWord_769982, baseEnd_769982] using wordTrace_append hprefix tailTrace_769982
  have hstable : (prefixWord ++ tailWord_769982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_769982).length < 2 ^ (prefixWord ++ tailWord_769982).sum := by decide
  have hdescent : baseEnd_769982 < baseStart_769982 := by decide
  rcases family_descends (prefixWord ++ tailWord_769982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770099 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3]
def baseStart_770099 : Nat := 118140960795 + 770099 * 2 ^ 59
def prefixEnd_770099 : Nat := 4983230072969 + 3 ^ 40 * 770099 * 2
def baseEnd_770099 : Nat := 395430938546887717820885

theorem tailTrace_770099 : CollatzResearch.WordTrace tailWord_770099 prefixEnd_770099 395430938546887717820885 := by
  unfold tailWord_770099
  simp only [CollatzResearch.WordTrace]
  refine ⟨28087818037070320283273351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18725212024713546855515567 28087818037070320283273351)
  ·
    refine ⟨42131727055605480424910027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28087818037070320283273351 42131727055605480424910027)
    ·
      refine ⟨63197590583408220637365041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42131727055605480424910027 63197590583408220637365041)
      ·
        refine ⟨47398192937556165478023781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63197590583408220637365041 47398192937556165478023781)
        ·
          refine ⟨8887161175791781027129459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47398192937556165478023781 8887161175791781027129459)
          ·
            refine ⟨13330741763687671540694189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8887161175791781027129459 13330741763687671540694189)
            ·
              refine ⟨4999028161382876827760321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13330741763687671540694189 4999028161382876827760321)
              ·
                refine ⟨3749271121037157620820241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999028161382876827760321 3749271121037157620820241)
                ·
                  refine ⟨2811953340777868215615181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3749271121037157620820241 2811953340777868215615181)
                  ·
                    refine ⟨1054482502791700580855693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2811953340777868215615181 1054482502791700580855693)
                    ·
                      refine ⟨395430938546887717820885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054482502791700580855693 395430938546887717820885)
                      ·
                        rfl

theorem cell23_770099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_770099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770099 prefixEnd_770099 := by exact prefixLift 770099
  have htrace : WordTrace (prefixWord ++ tailWord_770099) baseStart_770099 baseEnd_770099 := by
    simpa [prefixWord, tailWord_770099, baseEnd_770099] using wordTrace_append hprefix tailTrace_770099
  have hstable : (prefixWord ++ tailWord_770099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770099).length < 2 ^ (prefixWord ++ tailWord_770099).sum := by decide
  have hdescent : baseEnd_770099 < baseStart_770099 := by decide
  rcases family_descends (prefixWord ++ tailWord_770099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770156 : List Nat := [2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 4]
def baseStart_770156 : Nat := 118140960795 + 770156 * 2 ^ 59
def prefixEnd_770156 : Nat := 4983230072969 + 3 ^ 40 * 770156 * 2
def baseEnd_770156 : Nat := 395460206944193994808123

theorem tailTrace_770156 : CollatzResearch.WordTrace tailWord_770156 prefixEnd_770156 395460206944193994808123 := by
  unfold tailWord_770156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044948498931909509049161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18726597998575879345398881 14044948498931909509049161)
  ·
    refine ⟨10533711374198932131786871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14044948498931909509049161 10533711374198932131786871)
    ·
      refine ⟨15800567061298398197680307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10533711374198932131786871 15800567061298398197680307)
      ·
        refine ⟨23700850591947597296520461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15800567061298398197680307 23700850591947597296520461)
        ·
          refine ⟨8887818971980348986195173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23700850591947597296520461 8887818971980348986195173)
          ·
            refine ⟨1666466057246315434911595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8887818971980348986195173 1666466057246315434911595)
            ·
              refine ⟨2499699085869473152367393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666466057246315434911595 2499699085869473152367393)
              ·
                refine ⟨1874774314402104864275545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499699085869473152367393 1874774314402104864275545)
                ·
                  refine ⟨1406080735801578648206659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1874774314402104864275545 1406080735801578648206659)
                  ·
                    refine ⟨2109121103702367972309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1406080735801578648206659 2109121103702367972309989)
                    ·
                      refine ⟨395460206944193994808123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2109121103702367972309989 395460206944193994808123)
                      ·
                        rfl

theorem cell23_770156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_770156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770156 prefixEnd_770156 := by exact prefixLift 770156
  have htrace : WordTrace (prefixWord ++ tailWord_770156) baseStart_770156 baseEnd_770156 := by
    simpa [prefixWord, tailWord_770156, baseEnd_770156] using wordTrace_append hprefix tailTrace_770156
  have hstable : (prefixWord ++ tailWord_770156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770156).length < 2 ^ (prefixWord ++ tailWord_770156).sum := by decide
  have hdescent : baseEnd_770156 < baseStart_770156 := by decide
  rcases family_descends (prefixWord ++ tailWord_770156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_770249 : Nat := 118140960795 + 770249 * 2 ^ 59
def prefixEnd_770249 : Nat := 4983230072969 + 3 ^ 40 * 770249 * 2
def baseEnd_770249 : Nat := 395507960645062130945195

theorem tailTrace_770249 : CollatzResearch.WordTrace tailWord_770249 prefixEnd_770249 395507960645062130945195 := by
  unfold tailWord_770249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28093288986526895901233801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18728859324351263934155867 28093288986526895901233801)
  ·
    refine ⟨21069966739895171925925351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28093288986526895901233801 21069966739895171925925351)
    ·
      refine ⟨31604950109842757888888027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21069966739895171925925351 31604950109842757888888027)
      ·
        refine ⟨47407425164764136833332041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31604950109842757888888027 47407425164764136833332041)
        ·
          refine ⟨35555568873573102624999031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47407425164764136833332041 35555568873573102624999031)
          ·
            refine ⟨53333353310359653937498547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35555568873573102624999031 53333353310359653937498547)
            ·
              refine ⟨80000029965539480906247821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53333353310359653937498547 80000029965539480906247821)
              ·
                refine ⟨30000011237077305339842933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80000029965539480906247821 30000011237077305339842933)
                ·
                  refine ⟨2812501053475997375610275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30000011237077305339842933 2812501053475997375610275)
                  ·
                    refine ⟨4218751580213996063415413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2812501053475997375610275 4218751580213996063415413)
                    ·
                      refine ⟨395507960645062130945195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4218751580213996063415413 395507960645062130945195)
                      ·
                        rfl

theorem cell23_770249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_770249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770249 prefixEnd_770249 := by exact prefixLift 770249
  have htrace : WordTrace (prefixWord ++ tailWord_770249) baseStart_770249 baseEnd_770249 := by
    simpa [prefixWord, tailWord_770249, baseEnd_770249] using wordTrace_append hprefix tailTrace_770249
  have hstable : (prefixWord ++ tailWord_770249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770249).length < 2 ^ (prefixWord ++ tailWord_770249).sum := by decide
  have hdescent : baseEnd_770249 < baseStart_770249 := by decide
  rcases family_descends (prefixWord ++ tailWord_770249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770263 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_770263 : Nat := 118140960795 + 770263 * 2 ^ 59
def prefixEnd_770263 : Nat := 4983230072969 + 3 ^ 40 * 770263 * 2
def baseEnd_770263 : Nat := 395515149374225076170131

theorem tailTrace_770263 : CollatzResearch.WordTrace tailWord_770263 prefixEnd_770263 395515149374225076170131 := by
  unfold tailWord_770263
  simp only [CollatzResearch.WordTrace]
  refine ⟨28093799608476176292243443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18729199738984117528162295 28093799608476176292243443)
  ·
    refine ⟨42140699412714264438365165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28093799608476176292243443 42140699412714264438365165)
    ·
      refine ⟨15802762279767849164386937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42140699412714264438365165 15802762279767849164386937)
      ·
        refine ⟨11852071709825886873290203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15802762279767849164386937 11852071709825886873290203)
        ·
          refine ⟨17778107564738830309935305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11852071709825886873290203 17778107564738830309935305)
          ·
            refine ⟨13333580673554122732451479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17778107564738830309935305 13333580673554122732451479)
            ·
              refine ⟨20000371010331184098677219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13333580673554122732451479 20000371010331184098677219)
              ·
                refine ⟨30000556515496776148015829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20000371010331184098677219 30000556515496776148015829)
                ·
                  refine ⟨703138043331955690969121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30000556515496776148015829 703138043331955690969121)
                  ·
                    refine ⟨527353532498966768226841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703138043331955690969121 527353532498966768226841)
                    ·
                      refine ⟨395515149374225076170131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527353532498966768226841 395515149374225076170131)
                      ·
                        rfl

theorem cell23_770263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_770263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770263 prefixEnd_770263 := by exact prefixLift 770263
  have htrace : WordTrace (prefixWord ++ tailWord_770263) baseStart_770263 baseEnd_770263 := by
    simpa [prefixWord, tailWord_770263, baseEnd_770263] using wordTrace_append hprefix tailTrace_770263
  have hstable : (prefixWord ++ tailWord_770263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770263).length < 2 ^ (prefixWord ++ tailWord_770263).sum := by decide
  have hdescent : baseEnd_770263 < baseStart_770263 := by decide
  rcases family_descends (prefixWord ++ tailWord_770263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770280 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_770280 : Nat := 118140960795 + 770280 * 2 ^ 59
def prefixEnd_770280 : Nat := 4983230072969 + 3 ^ 40 * 770280 * 2
def baseEnd_770280 : Nat := 395523878545351509657553

theorem tailTrace_770280 : CollatzResearch.WordTrace tailWord_770280 prefixEnd_770280 395523878545351509657553 := by
  unfold tailWord_770280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047209824707294097806147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18729613099609725463741529 14047209824707294097806147)
  ·
    refine ⟨21070814737060941146709221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14047209824707294097806147 21070814737060941146709221)
    ·
      refine ⟨3950777763198926465007979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21070814737060941146709221 3950777763198926465007979)
      ·
        refine ⟨5926166644798389697511969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3950777763198926465007979 5926166644798389697511969)
        ·
          refine ⟨4444624983598792273133977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5926166644798389697511969 4444624983598792273133977)
          ·
            refine ⟨3333468737699094204850483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4444624983598792273133977 3333468737699094204850483)
            ·
              refine ⟨5000203106548641307275725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333468737699094204850483 5000203106548641307275725)
              ·
                refine ⟨1875076164955740490228397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000203106548641307275725 1875076164955740490228397)
                ·
                  refine ⟨703153561858402683835649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1875076164955740490228397 703153561858402683835649)
                  ·
                    refine ⟨527365171393802012876737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703153561858402683835649 527365171393802012876737)
                    ·
                      refine ⟨395523878545351509657553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527365171393802012876737 395523878545351509657553)
                      ·
                        rfl

theorem cell23_770280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_770280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770280 prefixEnd_770280 := by exact prefixLift 770280
  have htrace : WordTrace (prefixWord ++ tailWord_770280) baseStart_770280 baseEnd_770280 := by
    simpa [prefixWord, tailWord_770280, baseEnd_770280] using wordTrace_append hprefix tailTrace_770280
  have hstable : (prefixWord ++ tailWord_770280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770280).length < 2 ^ (prefixWord ++ tailWord_770280).sum := by decide
  have hdescent : baseEnd_770280 < baseStart_770280 := by decide
  rcases family_descends (prefixWord ++ tailWord_770280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770300 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_770300 : Nat := 118140960795 + 770300 * 2 ^ 59
def prefixEnd_770300 : Nat := 4983230072969 + 3 ^ 40 * 770300 * 2
def baseEnd_770300 : Nat := 395534148158441431407461

theorem tailTrace_770300 : CollatzResearch.WordTrace tailWord_770300 prefixEnd_770300 395534148158441431407461 := by
  unfold tailWord_770300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047574554671065805670177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18730099406228087740893569 14047574554671065805670177)
  ·
    refine ⟨10535680916003299354252633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14047574554671065805670177 10535680916003299354252633)
    ·
      refine ⟨7901760687002474515689475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10535680916003299354252633 7901760687002474515689475)
      ·
        refine ⟨11852641030503711773534213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7901760687002474515689475 11852641030503711773534213)
        ·
          refine ⟨2222370193219445957537665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11852641030503711773534213 2222370193219445957537665)
          ·
            refine ⟨1666777644914584468153249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222370193219445957537665 1666777644914584468153249)
            ·
              refine ⟨1250083233685938351114937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666777644914584468153249 1250083233685938351114937)
              ·
                refine ⟨937562425264453763336203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250083233685938351114937 937562425264453763336203)
                ·
                  refine ⟨1406343637896680645004305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937562425264453763336203 1406343637896680645004305)
                  ·
                    refine ⟨1054757728422510483753229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1406343637896680645004305 1054757728422510483753229)
                    ·
                      refine ⟨395534148158441431407461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054757728422510483753229 395534148158441431407461)
                      ·
                        rfl

theorem cell23_770300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_770300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770300 prefixEnd_770300 := by exact prefixLift 770300
  have htrace : WordTrace (prefixWord ++ tailWord_770300) baseStart_770300 baseEnd_770300 := by
    simpa [prefixWord, tailWord_770300, baseEnd_770300] using wordTrace_append hprefix tailTrace_770300
  have hstable : (prefixWord ++ tailWord_770300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770300).length < 2 ^ (prefixWord ++ tailWord_770300).sum := by decide
  have hdescent : baseEnd_770300 < baseStart_770300 := by decide
  rcases family_descends (prefixWord ++ tailWord_770300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770313 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 3]
def baseStart_770313 : Nat := 118140960795 + 770313 * 2 ^ 59
def prefixEnd_770313 : Nat := 4983230072969 + 3 ^ 40 * 770313 * 2
def baseEnd_770313 : Nat := 395540823406949880544901

theorem tailTrace_770313 : CollatzResearch.WordTrace tailWord_770313 prefixEnd_770313 395540823406949880544901 := by
  unfold tailWord_770313
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095623258295034831563593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18730415505530023221042395 28095623258295034831563593)
  ·
    refine ⟨21071717443721276123672695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28095623258295034831563593 21071717443721276123672695)
    ·
      refine ⟨31607576165581914185509043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21071717443721276123672695 31607576165581914185509043)
      ·
        refine ⟨47411364248372871278263565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31607576165581914185509043 47411364248372871278263565)
        ·
          refine ⟨17779261593139826729348837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47411364248372871278263565 17779261593139826729348837)
          ·
            refine ⟨3333611548713717511752907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17779261593139826729348837 3333611548713717511752907)
            ·
              refine ⟨5000417323070576267629361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333611548713717511752907 5000417323070576267629361)
              ·
                refine ⟨3750312992302932200722021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000417323070576267629361 3750312992302932200722021)
                ·
                  refine ⟨703183686056799787635379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3750312992302932200722021 703183686056799787635379)
                  ·
                    refine ⟨1054775529085199681453069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 703183686056799787635379 1054775529085199681453069)
                    ·
                      refine ⟨395540823406949880544901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054775529085199681453069 395540823406949880544901)
                      ·
                        rfl

theorem cell23_770313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 3].length) (baseStart_770313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770313 prefixEnd_770313 := by exact prefixLift 770313
  have htrace : WordTrace (prefixWord ++ tailWord_770313) baseStart_770313 baseEnd_770313 := by
    simpa [prefixWord, tailWord_770313, baseEnd_770313] using wordTrace_append hprefix tailTrace_770313
  have hstable : (prefixWord ++ tailWord_770313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770313).length < 2 ^ (prefixWord ++ tailWord_770313).sum := by decide
  have hdescent : baseEnd_770313 < baseStart_770313 := by decide
  rcases family_descends (prefixWord ++ tailWord_770313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770319 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_770319 : Nat := 118140960795 + 770319 * 2 ^ 59
def prefixEnd_770319 : Nat := 4983230072969 + 3 ^ 40 * 770319 * 2
def baseEnd_770319 : Nat := 395543904290876857069873

theorem tailTrace_770319 : CollatzResearch.WordTrace tailWord_770319 prefixEnd_770319 395543904290876857069873 := by
  unfold tailWord_770319
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095842096273297856282011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18730561397515531904188007 28095842096273297856282011)
  ·
    refine ⟨42143763144409946784423017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28095842096273297856282011 42143763144409946784423017)
    ·
      refine ⟨31607822358307460088317263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42143763144409946784423017 31607822358307460088317263)
      ·
        refine ⟨47411733537461190132475895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31607822358307460088317263 47411733537461190132475895)
        ·
          refine ⟨71117600306191785198713843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47411733537461190132475895 71117600306191785198713843)
          ·
            refine ⟨106676400459287677798070765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71117600306191785198713843 106676400459287677798070765)
            ·
              refine ⟨40003650172232879174276537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106676400459287677798070765 40003650172232879174276537)
              ·
                refine ⟨30002737629174659380707403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40003650172232879174276537 30002737629174659380707403)
                ·
                  refine ⟨45004106443761989071061105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30002737629174659380707403 45004106443761989071061105)
                  ·
                    refine ⟨33753079832821491803295829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45004106443761989071061105 33753079832821491803295829)
                    ·
                      refine ⟨395543904290876857069873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33753079832821491803295829 395543904290876857069873)
                      ·
                        rfl

theorem cell23_770319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_770319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770319 prefixEnd_770319 := by exact prefixLift 770319
  have htrace : WordTrace (prefixWord ++ tailWord_770319) baseStart_770319 baseEnd_770319 := by
    simpa [prefixWord, tailWord_770319, baseEnd_770319] using wordTrace_append hprefix tailTrace_770319
  have hstable : (prefixWord ++ tailWord_770319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770319).length < 2 ^ (prefixWord ++ tailWord_770319).sum := by decide
  have hdescent : baseEnd_770319 < baseStart_770319 := by decide
  rcases family_descends (prefixWord ++ tailWord_770319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770386 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_770386 : Nat := 118140960795 + 770386 * 2 ^ 59
def prefixEnd_770386 : Nat := 4983230072969 + 3 ^ 40 * 770386 * 2
def baseEnd_770386 : Nat := 395578307494728094932065

theorem tailTrace_770386 : CollatzResearch.WordTrace tailWord_770386 prefixEnd_770386 395578307494728094932065 := by
  unfold tailWord_770386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7024571446757642074742753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18732190524687045532647341 7024571446757642074742753)
  ·
    refine ⟨5268428585068231556057065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7024571446757642074742753 5268428585068231556057065)
    ·
      refine ⟨3951321438801173667042799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5268428585068231556057065 3951321438801173667042799)
      ·
        refine ⟨5926982158201760500564199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951321438801173667042799 5926982158201760500564199)
        ·
          refine ⟨8890473237302640750846299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926982158201760500564199 8890473237302640750846299)
          ·
            refine ⟨13335709855953961126269449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8890473237302640750846299 13335709855953961126269449)
            ·
              refine ⟨10001782391965470844702087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13335709855953961126269449 10001782391965470844702087)
              ·
                refine ⟨15002673587948206267053131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001782391965470844702087 15002673587948206267053131)
                ·
                  refine ⟨22504010381922309400579697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15002673587948206267053131 22504010381922309400579697)
                  ·
                    refine ⟨16878007786441732050434773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22504010381922309400579697 16878007786441732050434773)
                    ·
                      refine ⟨395578307494728094932065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16878007786441732050434773 395578307494728094932065)
                      ·
                        rfl

theorem cell23_770386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_770386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770386 prefixEnd_770386 := by exact prefixLift 770386
  have htrace : WordTrace (prefixWord ++ tailWord_770386) baseStart_770386 baseEnd_770386 := by
    simpa [prefixWord, tailWord_770386, baseEnd_770386] using wordTrace_append hprefix tailTrace_770386
  have hstable : (prefixWord ++ tailWord_770386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770386).length < 2 ^ (prefixWord ++ tailWord_770386).sum := by decide
  have hdescent : baseEnd_770386 < baseStart_770386 := by decide
  rcases family_descends (prefixWord ++ tailWord_770386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770403 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3]
def baseStart_770403 : Nat := 118140960795 + 770403 * 2 ^ 59
def prefixEnd_770403 : Nat := 4983230072969 + 3 ^ 40 * 770403 * 2
def baseEnd_770403 : Nat := 395587036665854528419487

theorem tailTrace_770403 : CollatzResearch.WordTrace tailWord_770403 prefixEnd_770403 395587036665854528419487 := by
  unfold tailWord_770403
  simp only [CollatzResearch.WordTrace]
  refine ⟨28098905827968980202339863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18732603885312653468226575 28098905827968980202339863)
  ·
    refine ⟨42148358741953470303509795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28098905827968980202339863 42148358741953470303509795)
    ·
      refine ⟨63222538112930205455264693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42148358741953470303509795 63222538112930205455264693)
      ·
        refine ⟨5927112948087206761431065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63222538112930205455264693 5927112948087206761431065)
        ·
          refine ⟨4445334711065405071073299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5927112948087206761431065 4445334711065405071073299)
          ·
            refine ⟨6668002066598107606609949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445334711065405071073299 6668002066598107606609949)
            ·
              refine ⟨2500500774974290352478731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6668002066598107606609949 2500500774974290352478731)
              ·
                refine ⟨3750751162461435528718097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500500774974290352478731 3750751162461435528718097)
                ·
                  refine ⟨2813063371846076646538573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3750751162461435528718097 2813063371846076646538573)
                  ·
                    refine ⟨1054898764442278742451965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2813063371846076646538573 1054898764442278742451965)
                    ·
                      refine ⟨395587036665854528419487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054898764442278742451965 395587036665854528419487)
                      ·
                        rfl

theorem cell23_770403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_770403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770403 prefixEnd_770403 := by exact prefixLift 770403
  have htrace : WordTrace (prefixWord ++ tailWord_770403) baseStart_770403 baseEnd_770403 := by
    simpa [prefixWord, tailWord_770403, baseEnd_770403] using wordTrace_append hprefix tailTrace_770403
  have hstable : (prefixWord ++ tailWord_770403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770403).length < 2 ^ (prefixWord ++ tailWord_770403).sum := by decide
  have hdescent : baseEnd_770403 < baseStart_770403 := by decide
  rcases family_descends (prefixWord ++ tailWord_770403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770463 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_770463 : Nat := 118140960795 + 770463 * 2 ^ 59
def prefixEnd_770463 : Nat := 4983230072969 + 3 ^ 40 * 770463 * 2
def baseEnd_770463 : Nat := 395617845505124293669211

theorem tailTrace_770463 : CollatzResearch.WordTrace tailWord_770463 prefixEnd_770463 395617845505124293669211 := by
  unfold tailWord_770463
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101094207751610449524043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18734062805167740299682695 28101094207751610449524043)
  ·
    refine ⟨42151641311627415674286065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28101094207751610449524043 42151641311627415674286065)
    ·
      refine ⟨31613730983720561755714549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42151641311627415674286065 31613730983720561755714549)
      ·
        refine ⟨2963787279723802664598239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31613730983720561755714549 2963787279723802664598239)
        ·
          refine ⟨4445680919585703996897359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963787279723802664598239 4445680919585703996897359)
          ·
            refine ⟨6668521379378555995346039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445680919585703996897359 6668521379378555995346039)
            ·
              refine ⟨10002782069067833993019059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6668521379378555995346039 10002782069067833993019059)
              ·
                refine ⟨15004173103601750989528589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10002782069067833993019059 15004173103601750989528589)
                ·
                  refine ⟨5626564913850656621073221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15004173103601750989528589 5626564913850656621073221)
                  ·
                    refine ⟨1054980921346998116451229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5626564913850656621073221 1054980921346998116451229)
                    ·
                      refine ⟨395617845505124293669211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1054980921346998116451229 395617845505124293669211)
                      ·
                        rfl

theorem cell23_770463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_770463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770463 prefixEnd_770463 := by exact prefixLift 770463
  have htrace : WordTrace (prefixWord ++ tailWord_770463) baseStart_770463 baseEnd_770463 := by
    simpa [prefixWord, tailWord_770463, baseEnd_770463] using wordTrace_append hprefix tailTrace_770463
  have hstable : (prefixWord ++ tailWord_770463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770463).length < 2 ^ (prefixWord ++ tailWord_770463).sum := by decide
  have hdescent : baseEnd_770463 < baseStart_770463 := by decide
  rcases family_descends (prefixWord ++ tailWord_770463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770487 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 1, 4]
def baseStart_770487 : Nat := 118140960795 + 770487 * 2 ^ 59
def prefixEnd_770487 : Nat := 4983230072969 + 3 ^ 40 * 770487 * 2
def baseEnd_770487 : Nat := 131876723013610733256367

theorem tailTrace_770487 : CollatzResearch.WordTrace tailWord_770487 prefixEnd_770487 131876723013610733256367 := by
  unfold tailWord_770487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101969559664662548397715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18734646373109775032265143 28101969559664662548397715)
  ·
    refine ⟨42152954339496993822596573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28101969559664662548397715 42152954339496993822596573)
    ·
      refine ⟨15807357877311372683473715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42152954339496993822596573 15807357877311372683473715)
      ·
        refine ⟨23711036815967059025210573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15807357877311372683473715 23711036815967059025210573)
        ·
          refine ⟨8891638805987647134453965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23711036815967059025210573 8891638805987647134453965)
          ·
            refine ⟨3334364552245367675420237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8891638805987647134453965 3334364552245367675420237)
            ·
              refine ⟨1250386707092012878282589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3334364552245367675420237 1250386707092012878282589)
              ·
                refine ⟨468895015159504829355971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1250386707092012878282589 468895015159504829355971)
                ·
                  refine ⟨703342522739257244033957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468895015159504829355971 703342522739257244033957)
                  ·
                    refine ⟨131876723013610733256367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 703342522739257244033957 131876723013610733256367)
                    ·
                      rfl

theorem cell23_770487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_770487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770487 prefixEnd_770487 := by exact prefixLift 770487
  have htrace : WordTrace (prefixWord ++ tailWord_770487) baseStart_770487 baseEnd_770487 := by
    simpa [prefixWord, tailWord_770487, baseEnd_770487] using wordTrace_append hprefix tailTrace_770487
  have hstable : (prefixWord ++ tailWord_770487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770487).length < 2 ^ (prefixWord ++ tailWord_770487).sum := by decide
  have hdescent : baseEnd_770487 < baseStart_770487 := by decide
  rcases family_descends (prefixWord ++ tailWord_770487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770504 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 1, 4]
def baseStart_770504 : Nat := 118140960795 + 770504 * 2 ^ 59
def prefixEnd_770504 : Nat := 4983230072969 + 3 ^ 40 * 770504 * 2
def baseEnd_770504 : Nat := 131879632737319544418841

theorem tailTrace_770504 : CollatzResearch.WordTrace tailWord_770504 prefixEnd_770504 131879632737319544418841 := by
  unfold tailWord_770504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051294800301537225883283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18735059733735382967844377 14051294800301537225883283)
  ·
    refine ⟨21076942200452305838824925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14051294800301537225883283 21076942200452305838824925)
    ·
      refine ⟨7903853325169614689559347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21076942200452305838824925 7903853325169614689559347)
      ·
        refine ⟨11855779987754422034339021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903853325169614689559347 11855779987754422034339021)
        ·
          refine ⟨4445917495407908262877133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11855779987754422034339021 4445917495407908262877133)
          ·
            refine ⟨1667219060777965598578925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4445917495407908262877133 1667219060777965598578925)
            ·
              refine ⟨625207147791737099467097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1667219060777965598578925 625207147791737099467097)
              ·
                refine ⟨468905360843802824600323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625207147791737099467097 468905360843802824600323)
                ·
                  refine ⟨703358041265704236900485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468905360843802824600323 703358041265704236900485)
                  ·
                    refine ⟨131879632737319544418841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 703358041265704236900485 131879632737319544418841)
                    ·
                      rfl

theorem cell23_770504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_770504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770504 prefixEnd_770504 := by exact prefixLift 770504
  have htrace : WordTrace (prefixWord ++ tailWord_770504) baseStart_770504 baseEnd_770504 := by
    simpa [prefixWord, tailWord_770504, baseEnd_770504] using wordTrace_append hprefix tailTrace_770504
  have hstable : (prefixWord ++ tailWord_770504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770504).length < 2 ^ (prefixWord ++ tailWord_770504).sum := by decide
  have hdescent : baseEnd_770504 < baseStart_770504 := by decide
  rcases family_descends (prefixWord ++ tailWord_770504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770517 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 6]
def baseStart_770517 : Nat := 118140960795 + 770517 * 2 ^ 59
def prefixEnd_770517 : Nat := 4983230072969 + 3 ^ 40 * 770517 * 2
def baseEnd_770517 : Nat := 43960619273385231377107

theorem tailTrace_770517 : CollatzResearch.WordTrace tailWord_770517 prefixEnd_770517 43960619273385231377107 := by
  unfold tailWord_770517
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103063749555977671989805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18735375833037318447993203 28103063749555977671989805)
  ·
    refine ⟨10538648906083491626996177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28103063749555977671989805 10538648906083491626996177)
    ·
      refine ⟨7903986679562618720247133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538648906083491626996177 7903986679562618720247133)
      ·
        refine ⟨2963995004835982020092675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7903986679562618720247133 2963995004835982020092675)
        ·
          refine ⟨4445992507253973030139013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963995004835982020092675 4445992507253973030139013)
          ·
            refine ⟨833623595110119943151065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4445992507253973030139013 833623595110119943151065)
            ·
              refine ⟨625217696332589957363299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 833623595110119943151065 625217696332589957363299)
              ·
                refine ⟨937826544498884936044949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625217696332589957363299 937826544498884936044949)
                ·
                  refine ⟨43960619273385231377107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 937826544498884936044949 43960619273385231377107)
                  ·
                    rfl

theorem cell23_770517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_770517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770517 prefixEnd_770517 := by exact prefixLift 770517
  have htrace : WordTrace (prefixWord ++ tailWord_770517) baseStart_770517 baseEnd_770517 := by
    simpa [prefixWord, tailWord_770517, baseEnd_770517] using wordTrace_append hprefix tailTrace_770517
  have hstable : (prefixWord ++ tailWord_770517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770517).length < 2 ^ (prefixWord ++ tailWord_770517).sum := by decide
  have hdescent : baseEnd_770517 < baseStart_770517 := by decide
  rcases family_descends (prefixWord ++ tailWord_770517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770520 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2]
def baseStart_770520 : Nat := 118140960795 + 770520 * 2 ^ 59
def prefixEnd_770520 : Nat := 4983230072969 + 3 ^ 40 * 770520 * 2
def baseEnd_770520 : Nat := 395647113902430570656449

theorem tailTrace_770520 : CollatzResearch.WordTrace tailWord_770520 prefixEnd_770520 395647113902430570656449 := by
  unfold tailWord_770520
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051586584272554592174507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18735448779030072789566009 14051586584272554592174507)
  ·
    refine ⟨21077379876408831888261761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14051586584272554592174507 21077379876408831888261761)
    ·
      refine ⟨15808034907306623916196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21077379876408831888261761 15808034907306623916196321)
      ·
        refine ⟨11856026180479967937147241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15808034907306623916196321 11856026180479967937147241)
        ·
          refine ⟨8892019635359975952860431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11856026180479967937147241 8892019635359975952860431)
          ·
            refine ⟨13338029453039963929290647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8892019635359975952860431 13338029453039963929290647)
            ·
              refine ⟨20007044179559945893935971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13338029453039963929290647 20007044179559945893935971)
              ·
                refine ⟨30010566269339918840903957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20007044179559945893935971 30010566269339918840903957)
                ·
                  refine ⟨1406745293875308695667373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30010566269339918840903957 1406745293875308695667373)
                  ·
                    refine ⟨527529485203240760875265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406745293875308695667373 527529485203240760875265)
                    ·
                      refine ⟨395647113902430570656449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527529485203240760875265 395647113902430570656449)
                      ·
                        rfl

theorem cell23_770520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_770520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770520 prefixEnd_770520 := by exact prefixLift 770520
  have htrace : WordTrace (prefixWord ++ tailWord_770520) baseStart_770520 baseEnd_770520 := by
    simpa [prefixWord, tailWord_770520, baseEnd_770520] using wordTrace_append hprefix tailTrace_770520
  have hstable : (prefixWord ++ tailWord_770520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770520).length < 2 ^ (prefixWord ++ tailWord_770520).sum := by decide
  have hdescent : baseEnd_770520 < baseStart_770520 := by decide
  rcases family_descends (prefixWord ++ tailWord_770520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770561 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_770561 : Nat := 118140960795 + 770561 * 2 ^ 59
def prefixEnd_770561 : Nat := 4983230072969 + 3 ^ 40 * 770561 * 2
def baseEnd_770561 : Nat := 395668166609264910243761

theorem tailTrace_770561 : CollatzResearch.WordTrace tailWord_770561 prefixEnd_770561 395668166609264910243761 := by
  unfold tailWord_770561
  simp only [CollatzResearch.WordTrace]
  refine ⟨28104668561396573186591537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18736445707597715457727691 28104668561396573186591537)
  ·
    refine ⟨21078501421047429889943653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28104668561396573186591537 21078501421047429889943653)
    ·
      refine ⟨3952219016446393104364435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21078501421047429889943653 3952219016446393104364435)
      ·
        refine ⟨5928328524669589656546653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952219016446393104364435 5928328524669589656546653)
        ·
          refine ⟨2223123196751096121204995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928328524669589656546653 2223123196751096121204995)
          ·
            refine ⟨3334684795126644181807493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223123196751096121204995 3334684795126644181807493)
            ·
              refine ⟨625253399086245784088905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3334684795126644181807493 625253399086245784088905)
              ·
                refine ⟨468940049314684338066679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625253399086245784088905 468940049314684338066679)
                ·
                  refine ⟨703410073972026507100019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468940049314684338066679 703410073972026507100019)
                  ·
                    refine ⟨1055115110958039760650029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 703410073972026507100019 1055115110958039760650029)
                    ·
                      refine ⟨395668166609264910243761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055115110958039760650029 395668166609264910243761)
                      ·
                        rfl

theorem cell23_770561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_770561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770561 prefixEnd_770561 := by exact prefixLift 770561
  have htrace : WordTrace (prefixWord ++ tailWord_770561) baseStart_770561 baseEnd_770561 := by
    simpa [prefixWord, tailWord_770561, baseEnd_770561] using wordTrace_append hprefix tailTrace_770561
  have hstable : (prefixWord ++ tailWord_770561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770561).length < 2 ^ (prefixWord ++ tailWord_770561).sum := by decide
  have hdescent : baseEnd_770561 < baseStart_770561 := by decide
  rcases family_descends (prefixWord ++ tailWord_770561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770563 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4]
def baseStart_770563 : Nat := 118140960795 + 770563 * 2 ^ 59
def prefixEnd_770563 : Nat := 4983230072969 + 3 ^ 40 * 770563 * 2
def baseEnd_770563 : Nat := 395669193570573902418751

theorem tailTrace_770563 : CollatzResearch.WordTrace tailWord_770563 prefixEnd_770563 395669193570573902418751 := by
  unfold tailWord_770563
  simp only [CollatzResearch.WordTrace]
  refine ⟨28104741507389327528164343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18736494338259551685442895 28104741507389327528164343)
  ·
    refine ⟨42157112261083991292246515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28104741507389327528164343 42157112261083991292246515)
    ·
      refine ⟨63235668391625986938369773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42157112261083991292246515 63235668391625986938369773)
      ·
        refine ⟨23713375646859745101888665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63235668391625986938369773 23713375646859745101888665)
        ·
          refine ⟨17785031735144808826416499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23713375646859745101888665 17785031735144808826416499)
          ·
            refine ⟨26677547602717213239624749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17785031735144808826416499 26677547602717213239624749)
            ·
              refine ⟨10004080351018954964859281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26677547602717213239624749 10004080351018954964859281)
              ·
                refine ⟨7503060263264216223644461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10004080351018954964859281 7503060263264216223644461)
                ·
                  refine ⟨2813647598724081083866673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7503060263264216223644461 2813647598724081083866673)
                  ·
                    refine ⟨2110235699043060812900005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2813647598724081083866673 2110235699043060812900005)
                    ·
                      refine ⟨395669193570573902418751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2110235699043060812900005 395669193570573902418751)
                      ·
                        rfl

theorem cell23_770563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_770563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770563 prefixEnd_770563 := by exact prefixLift 770563
  have htrace : WordTrace (prefixWord ++ tailWord_770563) baseStart_770563 baseEnd_770563 := by
    simpa [prefixWord, tailWord_770563, baseEnd_770563] using wordTrace_append hprefix tailTrace_770563
  have hstable : (prefixWord ++ tailWord_770563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770563).length < 2 ^ (prefixWord ++ tailWord_770563).sum := by decide
  have hdescent : baseEnd_770563 < baseStart_770563 := by decide
  rcases family_descends (prefixWord ++ tailWord_770563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770570 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3]
def baseStart_770570 : Nat := 118140960795 + 770570 * 2 ^ 59
def prefixEnd_770570 : Nat := 4983230072969 + 3 ^ 40 * 770570 * 2
def baseEnd_770570 : Nat := 395672787935155375031219

theorem tailTrace_770570 : CollatzResearch.WordTrace tailWord_770570 prefixEnd_770570 395672787935155375031219 := by
  unfold tailWord_770570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026249204590991930917291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18736664545575978482446109 7026249204590991930917291)
  ·
    refine ⟨10539373806886487896375937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7026249204590991930917291 10539373806886487896375937)
    ·
      refine ⟨7904530355164865922281953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10539373806886487896375937 7904530355164865922281953)
      ·
        refine ⟨5928397766373649441711465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904530355164865922281953 5928397766373649441711465)
        ·
          refine ⟨4446298324780237081283599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928397766373649441711465 4446298324780237081283599)
          ·
            refine ⟨6669447487170355621925399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446298324780237081283599 6669447487170355621925399)
            ·
              refine ⟨10004171230755533432888099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6669447487170355621925399 10004171230755533432888099)
              ·
                refine ⟨15006256846133300149332149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10004171230755533432888099 15006256846133300149332149)
                ·
                  refine ⟨1406836579324996888999889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15006256846133300149332149 1406836579324996888999889)
                  ·
                    refine ⟨1055127434493747666749917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1406836579324996888999889 1055127434493747666749917)
                    ·
                      refine ⟨395672787935155375031219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055127434493747666749917 395672787935155375031219)
                      ·
                        rfl

theorem cell23_770570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_770570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770570 prefixEnd_770570 := by exact prefixLift 770570
  have htrace : WordTrace (prefixWord ++ tailWord_770570) baseStart_770570 baseEnd_770570 := by
    simpa [prefixWord, tailWord_770570, baseEnd_770570] using wordTrace_append hprefix tailTrace_770570
  have hstable : (prefixWord ++ tailWord_770570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770570).length < 2 ^ (prefixWord ++ tailWord_770570).sum := by decide
  have hdescent : baseEnd_770570 < baseStart_770570 := by decide
  rcases family_descends (prefixWord ++ tailWord_770570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770584 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2]
def baseStart_770584 : Nat := 118140960795 + 770584 * 2 ^ 59
def prefixEnd_770584 : Nat := 4983230072969 + 3 ^ 40 * 770584 * 2
def baseEnd_770584 : Nat := 395679976664318320256155

theorem tailTrace_770584 : CollatzResearch.WordTrace tailWord_770584 prefixEnd_770584 395679976664318320256155 := by
  unfold tailWord_770584
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052753720156624057339403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18737004960208832076452537 14052753720156624057339403)
  ·
    refine ⟨21079130580234936086009105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14052753720156624057339403 21079130580234936086009105)
    ·
      refine ⟨15809347935176202064506829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21079130580234936086009105 15809347935176202064506829)
      ·
        refine ⟨5928505475691075774190061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15809347935176202064506829 5928505475691075774190061)
        ·
          refine ⟨2223189553384153415321273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928505475691075774190061 2223189553384153415321273)
          ·
            refine ⟨1667392165038115061490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223189553384153415321273 1667392165038115061490955)
            ·
              refine ⟨2501088247557172592236433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667392165038115061490955 2501088247557172592236433)
              ·
                refine ⟨1875816185667879444177325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501088247557172592236433 1875816185667879444177325)
                ·
                  refine ⟨703431069625454791566497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1875816185667879444177325 703431069625454791566497)
                  ·
                    refine ⟨527573302219091093674873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703431069625454791566497 527573302219091093674873)
                    ·
                      refine ⟨395679976664318320256155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527573302219091093674873 395679976664318320256155)
                      ·
                        rfl

theorem cell23_770584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_770584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770584 prefixEnd_770584 := by exact prefixLift 770584
  have htrace : WordTrace (prefixWord ++ tailWord_770584) baseStart_770584 baseEnd_770584 := by
    simpa [prefixWord, tailWord_770584, baseEnd_770584] using wordTrace_append hprefix tailTrace_770584
  have hstable : (prefixWord ++ tailWord_770584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770584).length < 2 ^ (prefixWord ++ tailWord_770584).sum := by decide
  have hdescent : baseEnd_770584 < baseStart_770584 := by decide
  rcases family_descends (prefixWord ++ tailWord_770584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770617 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 3]
def baseStart_770617 : Nat := 118140960795 + 770617 * 2 ^ 59
def prefixEnd_770617 : Nat := 4983230072969 + 3 ^ 40 * 770617 * 2
def baseEnd_770617 : Nat := 395696921525916691143503

theorem tailTrace_770617 : CollatzResearch.WordTrace tailWord_770617 prefixEnd_770617 395696921525916691143503 := by
  unfold tailWord_770617
  simp only [CollatzResearch.WordTrace]
  refine ⟨28106711049193694750630105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18737807366129129833753403 28106711049193694750630105)
  ·
    refine ⟨21080033286895271062972579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28106711049193694750630105 21080033286895271062972579)
    ·
      refine ⟨31620049930342906594458869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21080033286895271062972579 31620049930342906594458869)
      ·
        refine ⟨2964379680969647493230519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31620049930342906594458869 2964379680969647493230519)
        ·
          refine ⟨4446569521454471239845779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2964379680969647493230519 4446569521454471239845779)
          ·
            refine ⟨6669854282181706859768669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446569521454471239845779 6669854282181706859768669)
            ·
              refine ⟨2501195355818140072413251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6669854282181706859768669 2501195355818140072413251)
              ·
                refine ⟨3751793033727210108619877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501195355818140072413251 3751793033727210108619877)
                ·
                  refine ⟨703461193823851895366227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3751793033727210108619877 703461193823851895366227)
                  ·
                    refine ⟨1055191790735777843049341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 703461193823851895366227 1055191790735777843049341)
                    ·
                      refine ⟨395696921525916691143503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055191790735777843049341 395696921525916691143503)
                      ·
                        rfl

theorem cell23_770617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_770617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770617 prefixEnd_770617 := by exact prefixLift 770617
  have htrace : WordTrace (prefixWord ++ tailWord_770617) baseStart_770617 baseEnd_770617 := by
    simpa [prefixWord, tailWord_770617, baseEnd_770617] using wordTrace_append hprefix tailTrace_770617
  have hstable : (prefixWord ++ tailWord_770617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770617).length < 2 ^ (prefixWord ++ tailWord_770617).sum := by decide
  have hdescent : baseEnd_770617 < baseStart_770617 := by decide
  rcases family_descends (prefixWord ++ tailWord_770617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770628 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_770628 : Nat := 118140960795 + 770628 * 2 ^ 59
def prefixEnd_770628 : Nat := 4983230072969 + 3 ^ 40 * 770628 * 2
def baseEnd_770628 : Nat := 131900856604372049368651

theorem tailTrace_770628 : CollatzResearch.WordTrace tailWord_770628 prefixEnd_770628 131900856604372049368651 := by
  unfold tailWord_770628
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053556126076921814640269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18738074834769229086187025 14053556126076921814640269)
  ·
    refine ⟨5270083547278845680490101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14053556126076921814640269 5270083547278845680490101)
    ·
      refine ⟨494070332557391782545947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5270083547278845680490101 494070332557391782545947)
      ·
        refine ⟨741105498836087673818921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494070332557391782545947 741105498836087673818921)
        ·
          refine ⟨555829124127065755364191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741105498836087673818921 555829124127065755364191)
          ·
            refine ⟨833743686190598633046287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555829124127065755364191 833743686190598633046287)
            ·
              refine ⟨1250615529285897949569431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833743686190598633046287 1250615529285897949569431)
              ·
                refine ⟨1875923293928846924354147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250615529285897949569431 1875923293928846924354147)
                ·
                  refine ⟨2813884940893270386531221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875923293928846924354147 2813884940893270386531221)
                  ·
                    refine ⟨131900856604372049368651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2813884940893270386531221 131900856604372049368651)
                    ·
                      rfl

theorem cell23_770628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_770628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770628 prefixEnd_770628 := by exact prefixLift 770628
  have htrace : WordTrace (prefixWord ++ tailWord_770628) baseStart_770628 baseEnd_770628 := by
    simpa [prefixWord, tailWord_770628, baseEnd_770628] using wordTrace_append hprefix tailTrace_770628
  have hstable : (prefixWord ++ tailWord_770628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770628).length < 2 ^ (prefixWord ++ tailWord_770628).sum := by decide
  have hdescent : baseEnd_770628 < baseStart_770628 := by decide
  rcases family_descends (prefixWord ++ tailWord_770628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770644 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_770644 : Nat := 118140960795 + 770644 * 2 ^ 59
def prefixEnd_770644 : Nat := 4983230072969 + 3 ^ 40 * 770644 * 2
def baseEnd_770644 : Nat := 395710785503588085505879

theorem tailTrace_770644 : CollatzResearch.WordTrace tailWord_770644 prefixEnd_770644 395710785503588085505879 := by
  unfold tailWord_770644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14053847910047939180931493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18738463880063918907908657 14053847910047939180931493)
  ·
    refine ⟨2635096483133988596424655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14053847910047939180931493 2635096483133988596424655)
    ·
      refine ⟨3952644724700982894636983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635096483133988596424655 3952644724700982894636983)
      ·
        refine ⟨5928967087051474341955475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952644724700982894636983 5928967087051474341955475)
        ·
          refine ⟨8893450630577211512933213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928967087051474341955475 8893450630577211512933213)
          ·
            refine ⟨3335043986466454317349955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8893450630577211512933213 3335043986466454317349955)
            ·
              refine ⟨5002565979699681476024933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335043986466454317349955 5002565979699681476024933)
              ·
                refine ⟨937981121193690276754675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5002565979699681476024933 937981121193690276754675)
                ·
                  refine ⟨1406971681790535415132013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937981121193690276754675 1406971681790535415132013)
                  ·
                    refine ⟨527614380671450780674505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406971681790535415132013 527614380671450780674505)
                    ·
                      refine ⟨395710785503588085505879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527614380671450780674505 395710785503588085505879)
                      ·
                        rfl

theorem cell23_770644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_770644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770644 prefixEnd_770644 := by exact prefixLift 770644
  have htrace : WordTrace (prefixWord ++ tailWord_770644) baseStart_770644 baseEnd_770644 := by
    simpa [prefixWord, tailWord_770644, baseEnd_770644] using wordTrace_append hprefix tailTrace_770644
  have hstable : (prefixWord ++ tailWord_770644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770644).length < 2 ^ (prefixWord ++ tailWord_770644).sum := by decide
  have hdescent : baseEnd_770644 < baseStart_770644 := by decide
  rcases family_descends (prefixWord ++ tailWord_770644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770660 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 1, 5]
def baseStart_770660 : Nat := 118140960795 + 770660 * 2 ^ 59
def prefixEnd_770660 : Nat := 4983230072969 + 3 ^ 40 * 770660 * 2
def baseEnd_770660 : Nat := 395719001194060022905805

theorem tailTrace_770660 : CollatzResearch.WordTrace tailWord_770660 prefixEnd_770660 395719001194060022905805 := by
  unfold tailWord_770660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14054139694018956547222717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18738852925358608729630289 14054139694018956547222717)
  ·
    refine ⟨5270302385257108705208519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14054139694018956547222717 5270302385257108705208519)
    ·
      refine ⟨7905453577885663057812779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270302385257108705208519 7905453577885663057812779)
      ·
        refine ⟨11858180366828494586719169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7905453577885663057812779 11858180366828494586719169)
        ·
          refine ⟨8893635275121370940039377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11858180366828494586719169 8893635275121370940039377)
          ·
            refine ⟨6670226456341028205029533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8893635275121370940039377 6670226456341028205029533)
            ·
              refine ⟨2501334921127885576886075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6670226456341028205029533 2501334921127885576886075)
              ·
                refine ⟨3752002381691828365329113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501334921127885576886075 3752002381691828365329113)
                ·
                  refine ⟨2814001786268871273996835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752002381691828365329113 2814001786268871273996835)
                  ·
                    refine ⟨4221002679403306910995253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2814001786268871273996835 4221002679403306910995253)
                    ·
                      refine ⟨395719001194060022905805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4221002679403306910995253 395719001194060022905805)
                      ·
                        rfl

theorem cell23_770660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_770660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770660 prefixEnd_770660 := by exact prefixLift 770660
  have htrace : WordTrace (prefixWord ++ tailWord_770660) baseStart_770660 baseEnd_770660 := by
    simpa [prefixWord, tailWord_770660, baseEnd_770660] using wordTrace_append hprefix tailTrace_770660
  have hstable : (prefixWord ++ tailWord_770660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770660).length < 2 ^ (prefixWord ++ tailWord_770660).sum := by decide
  have hdescent : baseEnd_770660 < baseStart_770660 := by decide
  rcases family_descends (prefixWord ++ tailWord_770660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770683 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8]
def baseStart_770683 : Nat := 118140960795 + 770683 * 2 ^ 59
def prefixEnd_770683 : Nat := 4983230072969 + 3 ^ 40 * 770683 * 2
def baseEnd_770683 : Nat := 395730811249113432918199

theorem tailTrace_770683 : CollatzResearch.WordTrace tailWord_770683 prefixEnd_770683 395730811249113432918199 := by
  unfold tailWord_770683
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109118266954588022532703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18739412177969725348355135 28109118266954588022532703)
  ·
    refine ⟨42163677400431882033799055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109118266954588022532703 42163677400431882033799055)
    ·
      refine ⟨63245516100647823050698583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42163677400431882033799055 63245516100647823050698583)
      ·
        refine ⟨94868274150971734576047875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63245516100647823050698583 94868274150971734576047875)
        ·
          refine ⟨142302411226457601864071813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94868274150971734576047875 142302411226457601864071813)
          ·
            refine ⟨26681702104960800349513465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142302411226457601864071813 26681702104960800349513465)
            ·
              refine ⟨20011276578720600262135099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26681702104960800349513465 20011276578720600262135099)
              ·
                refine ⟨30016914868080900393202649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20011276578720600262135099 30016914868080900393202649)
                ·
                  refine ⟨22512686151060675294901987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30016914868080900393202649 22512686151060675294901987)
                  ·
                    refine ⟨33769029226591012942352981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22512686151060675294901987 33769029226591012942352981)
                    ·
                      refine ⟨395730811249113432918199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 33769029226591012942352981 395730811249113432918199)
                      ·
                        rfl

theorem cell23_770683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_770683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770683 prefixEnd_770683 := by exact prefixLift 770683
  have htrace : WordTrace (prefixWord ++ tailWord_770683) baseStart_770683 baseEnd_770683 := by
    simpa [prefixWord, tailWord_770683, baseEnd_770683] using wordTrace_append hprefix tailTrace_770683
  have hstable : (prefixWord ++ tailWord_770683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770683).length < 2 ^ (prefixWord ++ tailWord_770683).sum := by decide
  have hdescent : baseEnd_770683 < baseStart_770683 := by decide
  rcases family_descends (prefixWord ++ tailWord_770683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770691 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 2, 2, 2]
def baseStart_770691 : Nat := 118140960795 + 770691 * 2 ^ 59
def prefixEnd_770691 : Nat := 4983230072969 + 3 ^ 40 * 770691 * 2
def baseEnd_770691 : Nat := 395734919094349401618163

theorem tailTrace_770691 : CollatzResearch.WordTrace tailWord_770691 prefixEnd_770691 395734919094349401618163 := by
  unfold tailWord_770691
  simp only [CollatzResearch.WordTrace]
  refine ⟨28109410050925605388823927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18739606700617070259215951 28109410050925605388823927)
  ·
    refine ⟨42164115076388408083235891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28109410050925605388823927 42164115076388408083235891)
    ·
      refine ⟨63246172614582612124853837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42164115076388408083235891 63246172614582612124853837)
      ·
        refine ⟨23717314730468479546820189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63246172614582612124853837 23717314730468479546820189)
        ·
          refine ⟨8893993023925679830057571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23717314730468479546820189 8893993023925679830057571)
          ·
            refine ⟨13340989535888519745086357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893993023925679830057571 13340989535888519745086357)
            ·
              refine ⟨625358884494774363050923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13340989535888519745086357 625358884494774363050923)
              ·
                refine ⟨938038326742161544576385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625358884494774363050923 938038326742161544576385)
                ·
                  refine ⟨703528745056621158432289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938038326742161544576385 703528745056621158432289)
                  ·
                    refine ⟨527646558792465868824217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703528745056621158432289 527646558792465868824217)
                    ·
                      refine ⟨395734919094349401618163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527646558792465868824217 395734919094349401618163)
                      ·
                        rfl

theorem cell23_770691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 2, 2, 2].length) (baseStart_770691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770691 prefixEnd_770691 := by exact prefixLift 770691
  have htrace : WordTrace (prefixWord ++ tailWord_770691) baseStart_770691 baseEnd_770691 := by
    simpa [prefixWord, tailWord_770691, baseEnd_770691] using wordTrace_append hprefix tailTrace_770691
  have hstable : (prefixWord ++ tailWord_770691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770691).length < 2 ^ (prefixWord ++ tailWord_770691).sum := by decide
  have hdescent : baseEnd_770691 < baseStart_770691 := by decide
  rcases family_descends (prefixWord ++ tailWord_770691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770764 : List Nat := [2, 2, 1, 5, 1, 1, 3, 1, 2, 1, 4]
def baseStart_770764 : Nat := 118140960795 + 770764 * 2 ^ 59
def prefixEnd_770764 : Nat := 4983230072969 + 3 ^ 40 * 770764 * 2
def baseEnd_770764 : Nat := 395772403182127616005327

theorem tailTrace_770764 : CollatzResearch.WordTrace tailWord_770764 prefixEnd_770764 395772403182127616005327 := by
  unfold tailWord_770764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056036289830569428115673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18741381719774092570820897 14056036289830569428115673)
  ·
    refine ⟨10542027217372927071086755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14056036289830569428115673 10542027217372927071086755)
    ·
      refine ⟨15813040826059390606630133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10542027217372927071086755 15813040826059390606630133)
      ·
        refine ⟨1482472577443067869371575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15813040826059390606630133 1482472577443067869371575)
        ·
          refine ⟨2223708866164601804057363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482472577443067869371575 2223708866164601804057363)
          ·
            refine ⟨3335563299246902706086045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223708866164601804057363 3335563299246902706086045)
            ·
              refine ⟨1250836237217588514782267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3335563299246902706086045 1250836237217588514782267)
              ·
                refine ⟨1876254355826382772173401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250836237217588514782267 1876254355826382772173401)
                ·
                  refine ⟨1407190766869787079130051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1876254355826382772173401 1407190766869787079130051)
                  ·
                    refine ⟨2110786150304680618695077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1407190766869787079130051 2110786150304680618695077)
                    ·
                      refine ⟨395772403182127616005327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2110786150304680618695077 395772403182127616005327)
                      ·
                        rfl

theorem cell23_770764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_770764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770764 prefixEnd_770764 := by exact prefixLift 770764
  have htrace : WordTrace (prefixWord ++ tailWord_770764) baseStart_770764 baseEnd_770764 := by
    simpa [prefixWord, tailWord_770764, baseEnd_770764] using wordTrace_append hprefix tailTrace_770764
  have hstable : (prefixWord ++ tailWord_770764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770764).length < 2 ^ (prefixWord ++ tailWord_770764).sum := by decide
  have hdescent : baseEnd_770764 < baseStart_770764 := by decide
  rcases family_descends (prefixWord ++ tailWord_770764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770787 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 8]
def baseStart_770787 : Nat := 118140960795 + 770787 * 2 ^ 59
def prefixEnd_770787 : Nat := 4983230072969 + 3 ^ 40 * 770787 * 2
def baseEnd_770787 : Nat := 43976023693020114001969

theorem tailTrace_770787 : CollatzResearch.WordTrace tailWord_770787 prefixEnd_770787 43976023693020114001969 := by
  unfold tailWord_770787
  simp only [CollatzResearch.WordTrace]
  refine ⟨28112911458577813784318615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18741940972385209189545743 28112911458577813784318615)
  ·
    refine ⟨42169367187866720676477923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28112911458577813784318615 42169367187866720676477923)
    ·
      refine ⟨63254050781800081014716885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42169367187866720676477923 63254050781800081014716885)
      ·
        refine ⟨1482516815198439398782427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63254050781800081014716885 1482516815198439398782427)
        ·
          refine ⟨2223775222797659098173641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482516815198439398782427 2223775222797659098173641)
          ·
            refine ⟨1667831417098244323630231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223775222797659098173641 1667831417098244323630231)
            ·
              refine ⟨2501747125647366485445347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667831417098244323630231 2501747125647366485445347)
              ·
                refine ⟨3752620688471049728168021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501747125647366485445347 3752620688471049728168021)
                ·
                  refine ⟨43976023693020114001969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3752620688471049728168021 43976023693020114001969)
                  ·
                    rfl

theorem cell23_770787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 8].length) (baseStart_770787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770787 prefixEnd_770787 := by exact prefixLift 770787
  have htrace : WordTrace (prefixWord ++ tailWord_770787) baseStart_770787 baseEnd_770787 := by
    simpa [prefixWord, tailWord_770787, baseEnd_770787] using wordTrace_append hprefix tailTrace_770787
  have hstable : (prefixWord ++ tailWord_770787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770787).length < 2 ^ (prefixWord ++ tailWord_770787).sum := by decide
  have hdescent : baseEnd_770787 < baseStart_770787 := by decide
  rcases family_descends (prefixWord ++ tailWord_770787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770810 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_770810 : Nat := 118140960795 + 770810 * 2 ^ 59
def prefixEnd_770810 : Nat := 4983230072969 + 3 ^ 40 * 770810 * 2
def baseEnd_770810 : Nat := 395796023292234436030115

theorem tailTrace_770810 : CollatzResearch.WordTrace tailWord_770810 prefixEnd_770810 395796023292234436030115 := by
  unfold tailWord_770810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028437584373622178101471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18742500224996325808270589 7028437584373622178101471)
  ·
    refine ⟨10542656376560433267152207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7028437584373622178101471 10542656376560433267152207)
    ·
      refine ⟨15813984564840649900728311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10542656376560433267152207 15813984564840649900728311)
      ·
        refine ⟨23720976847260974851092467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15813984564840649900728311 23720976847260974851092467)
        ·
          refine ⟨35581465270891462276638701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23720976847260974851092467 35581465270891462276638701)
          ·
            refine ⟨13343049476584298353739513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35581465270891462276638701 13343049476584298353739513)
            ·
              refine ⟨10007287107438223765304635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13343049476584298353739513 10007287107438223765304635)
              ·
                refine ⟨15010930661157335647956953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10007287107438223765304635 15010930661157335647956953)
                ·
                  refine ⟨11258197995868001735967715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15010930661157335647956953 11258197995868001735967715)
                  ·
                    refine ⟨16887296993802002603951573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11258197995868001735967715 16887296993802002603951573)
                    ·
                      refine ⟨395796023292234436030115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16887296993802002603951573 395796023292234436030115)
                      ·
                        rfl

theorem cell23_770810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_770810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770810 prefixEnd_770810 := by exact prefixLift 770810
  have htrace : WordTrace (prefixWord ++ tailWord_770810) baseStart_770810 baseEnd_770810 := by
    simpa [prefixWord, tailWord_770810, baseEnd_770810] using wordTrace_append hprefix tailTrace_770810
  have hstable : (prefixWord ++ tailWord_770810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770810).length < 2 ^ (prefixWord ++ tailWord_770810).sum := by decide
  have hdescent : baseEnd_770810 < baseStart_770810 := by decide
  rcases family_descends (prefixWord ++ tailWord_770810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770824 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_770824 : Nat := 118140960795 + 770824 * 2 ^ 59
def prefixEnd_770824 : Nat := 4983230072969 + 3 ^ 40 * 770824 * 2
def baseEnd_770824 : Nat := 395803212021397381255051

theorem tailTrace_770824 : CollatzResearch.WordTrace tailWord_770824 prefixEnd_770824 395803212021397381255051 := by
  unfold tailWord_770824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057130479721884551707763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18742840639629179402277017 14057130479721884551707763)
  ·
    refine ⟨21085695719582826827561645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14057130479721884551707763 21085695719582826827561645)
    ·
      refine ⟨7907135894843560060335617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21085695719582826827561645 7907135894843560060335617)
      ·
        refine ⟨5930351921132670045251713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7907135894843560060335617 5930351921132670045251713)
        ·
          refine ⟨4447763940849502533938785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930351921132670045251713 4447763940849502533938785)
          ·
            refine ⟨3335822955637126900454089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4447763940849502533938785 3335822955637126900454089)
            ·
              refine ⟨2501867216727845175340567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335822955637126900454089 2501867216727845175340567)
              ·
                refine ⟨3752800825091767763010851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501867216727845175340567 3752800825091767763010851)
                ·
                  refine ⟨5629201237637651644516277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3752800825091767763010851 5629201237637651644516277)
                  ·
                    refine ⟨527737616028529841673401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5629201237637651644516277 527737616028529841673401)
                    ·
                      refine ⟨395803212021397381255051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527737616028529841673401 395803212021397381255051)
                      ·
                        rfl

theorem cell23_770824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_770824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770824 prefixEnd_770824 := by exact prefixLift 770824
  have htrace : WordTrace (prefixWord ++ tailWord_770824) baseStart_770824 baseEnd_770824 := by
    simpa [prefixWord, tailWord_770824, baseEnd_770824] using wordTrace_append hprefix tailTrace_770824
  have hstable : (prefixWord ++ tailWord_770824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770824).length < 2 ^ (prefixWord ++ tailWord_770824).sum := by decide
  have hdescent : baseEnd_770824 < baseStart_770824 := by decide
  rcases family_descends (prefixWord ++ tailWord_770824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770857 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 3]
def baseStart_770857 : Nat := 118140960795 + 770857 * 2 ^ 59
def prefixEnd_770857 : Nat := 4983230072969 + 3 ^ 40 * 770857 * 2
def baseEnd_770857 : Nat := 395820156882995752142399

theorem tailTrace_770857 : CollatzResearch.WordTrace tailWord_770857 prefixEnd_770857 395820156882995752142399 := by
  unfold tailWord_770857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115464568324215739366825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18743643045549477159577883 28115464568324215739366825)
  ·
    refine ⟨21086598426243161804525119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28115464568324215739366825 21086598426243161804525119)
    ·
      refine ⟨31629897639364742706787679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086598426243161804525119 31629897639364742706787679)
      ·
        refine ⟨47444846459047114060181519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31629897639364742706787679 47444846459047114060181519)
        ·
          refine ⟨71167269688570671090272279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47444846459047114060181519 71167269688570671090272279)
          ·
            refine ⟨106750904532856006635408419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71167269688570671090272279 106750904532856006635408419)
            ·
              refine ⟨160126356799284009953112629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106750904532856006635408419 160126356799284009953112629)
              ·
                refine ⟨15011845949932875933104309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160126356799284009953112629 15011845949932875933104309)
                ·
                  refine ⟨1407360557806207118728529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15011845949932875933104309 1407360557806207118728529)
                  ·
                    refine ⟨1055520418354655339046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1407360557806207118728529 1055520418354655339046397)
                    ·
                      refine ⟨395820156882995752142399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055520418354655339046397 395820156882995752142399)
                      ·
                        rfl

theorem cell23_770857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 3].length) (baseStart_770857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770857 prefixEnd_770857 := by exact prefixLift 770857
  have htrace : WordTrace (prefixWord ++ tailWord_770857) baseStart_770857 baseEnd_770857 := by
    simpa [prefixWord, tailWord_770857, baseEnd_770857] using wordTrace_append hprefix tailTrace_770857
  have hstable : (prefixWord ++ tailWord_770857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770857).length < 2 ^ (prefixWord ++ tailWord_770857).sum := by decide
  have hdescent : baseEnd_770857 < baseStart_770857 := by decide
  rcases family_descends (prefixWord ++ tailWord_770857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770867 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6]
def baseStart_770867 : Nat := 118140960795 + 770867 * 2 ^ 59
def prefixEnd_770867 : Nat := 4983230072969 + 3 ^ 40 * 770867 * 2
def baseEnd_770867 : Nat := 395825291689540713017353

theorem tailTrace_770867 : CollatzResearch.WordTrace tailWord_770867 prefixEnd_770867 395825291689540713017353 := by
  unfold tailWord_770867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115829298287987447230855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18743886198858658298153903 28115829298287987447230855)
  ·
    refine ⟨42173743947431981170846283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28115829298287987447230855 42173743947431981170846283)
    ·
      refine ⟨63260615921147971756269425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42173743947431981170846283 63260615921147971756269425)
      ·
        refine ⟨47445461940860978817202069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63260615921147971756269425 47445461940860978817202069)
        ·
          refine ⟨2224006028477858382056347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47445461940860978817202069 2224006028477858382056347)
          ·
            refine ⟨3336009042716787573084521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224006028477858382056347 3336009042716787573084521)
            ·
              refine ⟨2502006782037590679813391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3336009042716787573084521 2502006782037590679813391)
              ·
                refine ⟨3753010173056386019720087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2502006782037590679813391 3753010173056386019720087)
                ·
                  refine ⟨5629515259584579029580131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753010173056386019720087 5629515259584579029580131)
                  ·
                    refine ⟨8444272889376868544370197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5629515259584579029580131 8444272889376868544370197)
                    ·
                      refine ⟨395825291689540713017353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8444272889376868544370197 395825291689540713017353)
                      ·
                        rfl

theorem cell23_770867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_770867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770867 prefixEnd_770867 := by exact prefixLift 770867
  have htrace : WordTrace (prefixWord ++ tailWord_770867) baseStart_770867 baseEnd_770867 := by
    simpa [prefixWord, tailWord_770867, baseEnd_770867] using wordTrace_append hprefix tailTrace_770867
  have hstable : (prefixWord ++ tailWord_770867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770867).length < 2 ^ (prefixWord ++ tailWord_770867).sum := by decide
  have hdescent : baseEnd_770867 < baseStart_770867 := by decide
  rcases family_descends (prefixWord ++ tailWord_770867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770868 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_770868 : Nat := 118140960795 + 770868 * 2 ^ 59
def prefixEnd_770868 : Nat := 4983230072969 + 3 ^ 40 * 770868 * 2
def baseEnd_770868 : Nat := 131941935056731736368283

theorem tailTrace_770868 : CollatzResearch.WordTrace tailWord_770868 prefixEnd_770868 131941935056731736368283 := by
  unfold tailWord_770868
  simp only [CollatzResearch.WordTrace]
  refine ⟨14057932885642182309008629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18743910514189576412011505 14057932885642182309008629)
  ·
    refine ⟨1317931208028954591469559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14057932885642182309008629 1317931208028954591469559)
    ·
      refine ⟨1976896812043431887204339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1317931208028954591469559 1976896812043431887204339)
      ·
        refine ⟨2965345218065147830806509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1976896812043431887204339 2965345218065147830806509)
        ·
          refine ⟨1112004456774430436552441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2965345218065147830806509 1112004456774430436552441)
          ·
            refine ⟨834003342580822827414331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112004456774430436552441 834003342580822827414331)
            ·
              refine ⟨1251005013871234241121497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834003342580822827414331 1251005013871234241121497)
              ·
                refine ⟨938253760403425680841123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251005013871234241121497 938253760403425680841123)
                ·
                  refine ⟨1407380640605138521261685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938253760403425680841123 1407380640605138521261685)
                  ·
                    refine ⟨131941935056731736368283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1407380640605138521261685 131941935056731736368283)
                    ·
                      rfl

theorem cell23_770868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_770868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770868 prefixEnd_770868 := by exact prefixLift 770868
  have htrace : WordTrace (prefixWord ++ tailWord_770868) baseStart_770868 baseEnd_770868 := by
    simpa [prefixWord, tailWord_770868, baseEnd_770868] using wordTrace_append hprefix tailTrace_770868
  have hstable : (prefixWord ++ tailWord_770868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770868).length < 2 ^ (prefixWord ++ tailWord_770868).sum := by decide
  have hdescent : baseEnd_770868 < baseStart_770868 := by decide
  rcases family_descends (prefixWord ++ tailWord_770868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770881 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 1, 6]
def baseStart_770881 : Nat := 118140960795 + 770881 * 2 ^ 59
def prefixEnd_770881 : Nat := 4983230072969 + 3 ^ 40 * 770881 * 2
def baseEnd_770881 : Nat := 131944160139567886080763

theorem tailTrace_770881 : CollatzResearch.WordTrace tailWord_770881 prefixEnd_770881 131944160139567886080763 := by
  unfold tailWord_770881
  simp only [CollatzResearch.WordTrace]
  refine ⟨28116339920237267838240497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18744226613491511892160331 28116339920237267838240497)
  ·
    refine ⟨21087254940177950878680373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28116339920237267838240497 21087254940177950878680373)
    ·
      refine ⟨1976930150641682894876285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21087254940177950878680373 1976930150641682894876285)
      ·
        refine ⟨741348806490631085578607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1976930150641682894876285 741348806490631085578607)
        ·
          refine ⟨1112023209735946628367911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741348806490631085578607 1112023209735946628367911)
          ·
            refine ⟨1668034814603919942551867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112023209735946628367911 1668034814603919942551867)
            ·
              refine ⟨2502052221905879913827801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668034814603919942551867 2502052221905879913827801)
              ·
                refine ⟨1876539166429409935370851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502052221905879913827801 1876539166429409935370851)
                ·
                  refine ⟨2814808749644114903056277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876539166429409935370851 2814808749644114903056277)
                  ·
                    refine ⟨131944160139567886080763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2814808749644114903056277 131944160139567886080763)
                    ·
                      rfl

theorem cell23_770881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_770881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770881 prefixEnd_770881 := by exact prefixLift 770881
  have htrace : WordTrace (prefixWord ++ tailWord_770881) baseStart_770881 baseEnd_770881 := by
    simpa [prefixWord, tailWord_770881, baseEnd_770881] using wordTrace_append hprefix tailTrace_770881
  have hstable : (prefixWord ++ tailWord_770881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770881).length < 2 ^ (prefixWord ++ tailWord_770881).sum := by decide
  have hdescent : baseEnd_770881 < baseStart_770881 := by decide
  rcases family_descends (prefixWord ++ tailWord_770881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770888 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_770888 : Nat := 118140960795 + 770888 * 2 ^ 59
def prefixEnd_770888 : Nat := 4983230072969 + 3 ^ 40 * 770888 * 2
def baseEnd_770888 : Nat := 395836074783285130854757

theorem tailTrace_770888 : CollatzResearch.WordTrace tailWord_770888 prefixEnd_770888 395836074783285130854757 := by
  unfold tailWord_770888
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058297615605954016872659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18744396820807938689163545 14058297615605954016872659)
  ·
    refine ⟨21087446423408931025308989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058297615605954016872659 21087446423408931025308989)
    ·
      refine ⟨7907792408778349134490871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21087446423408931025308989 7907792408778349134490871)
      ·
        refine ⟨11861688613167523701736307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7907792408778349134490871 11861688613167523701736307)
        ·
          refine ⟨17792532919751285552604461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861688613167523701736307 17792532919751285552604461)
          ·
            refine ⟨6672199844906732082226673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17792532919751285552604461 6672199844906732082226673)
            ·
              refine ⟨5004149883680049061670005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672199844906732082226673 5004149883680049061670005)
              ·
                refine ⟨469139051595004599531563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5004149883680049061670005 469139051595004599531563)
                ·
                  refine ⟨703708577392506899297345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469139051595004599531563 703708577392506899297345)
                  ·
                    refine ⟨527781433044380174473009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703708577392506899297345 527781433044380174473009)
                    ·
                      refine ⟨395836074783285130854757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527781433044380174473009 395836074783285130854757)
                      ·
                        rfl

theorem cell23_770888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_770888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770888 prefixEnd_770888 := by exact prefixLift 770888
  have htrace : WordTrace (prefixWord ++ tailWord_770888) baseStart_770888 baseEnd_770888 := by
    simpa [prefixWord, tailWord_770888, baseEnd_770888] using wordTrace_append hprefix tailTrace_770888
  have hstable : (prefixWord ++ tailWord_770888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770888).length < 2 ^ (prefixWord ++ tailWord_770888).sum := by decide
  have hdescent : baseEnd_770888 < baseStart_770888 := by decide
  rcases family_descends (prefixWord ++ tailWord_770888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770904 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3]
def baseStart_770904 : Nat := 118140960795 + 770904 * 2 ^ 59
def prefixEnd_770904 : Nat := 4983230072969 + 3 ^ 40 * 770904 * 2
def baseEnd_770904 : Nat := 395844290473757068254683

theorem tailTrace_770904 : CollatzResearch.WordTrace tailWord_770904 prefixEnd_770904 395844290473757068254683 := by
  unfold tailWord_770904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058589399576971383163883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18744785866102628510885177 14058589399576971383163883)
  ·
    refine ⟨21087884099365457074745825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058589399576971383163883 21087884099365457074745825)
    ·
      refine ⟨15815913074524092806059369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21087884099365457074745825 15815913074524092806059369)
      ·
        refine ⟨11861934805893069604544527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15815913074524092806059369 11861934805893069604544527)
        ·
          refine ⟨17792902208839604406816791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11861934805893069604544527 17792902208839604406816791)
          ·
            refine ⟨26689353313259406610225187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792902208839604406816791 26689353313259406610225187)
            ·
              refine ⟨40034029969889109915337781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26689353313259406610225187 40034029969889109915337781)
              ·
                refine ⟨3753190309677104054562917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40034029969889109915337781 3753190309677104054562917)
                ·
                  refine ⟨703723183064457010230547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3753190309677104054562917 703723183064457010230547)
                  ·
                    refine ⟨1055584774596685515345821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 703723183064457010230547 1055584774596685515345821)
                    ·
                      refine ⟨395844290473757068254683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055584774596685515345821 395844290473757068254683)
                      ·
                        rfl

theorem cell23_770904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_770904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770904 prefixEnd_770904 := by exact prefixLift 770904
  have htrace : WordTrace (prefixWord ++ tailWord_770904) baseStart_770904 baseEnd_770904 := by
    simpa [prefixWord, tailWord_770904, baseEnd_770904] using wordTrace_append hprefix tailTrace_770904
  have hstable : (prefixWord ++ tailWord_770904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770904).length < 2 ^ (prefixWord ++ tailWord_770904).sum := by decide
  have hdescent : baseEnd_770904 < baseStart_770904 := by decide
  rcases family_descends (prefixWord ++ tailWord_770904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770905 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 1, 2, 2]
def baseStart_770905 : Nat := 118140960795 + 770905 * 2 ^ 59
def prefixEnd_770905 : Nat := 4983230072969 + 3 ^ 40 * 770905 * 2
def baseEnd_770905 : Nat := 395844803954411564342179

theorem tailTrace_770905 : CollatzResearch.WordTrace tailWord_770905 prefixEnd_770905 395844803954411564342179 := by
  unfold tailWord_770905
  simp only [CollatzResearch.WordTrace]
  refine ⟨28117215272150319937114169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18744810181433546624742779 28117215272150319937114169)
  ·
    refine ⟨21087911454112739952835627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28117215272150319937114169 21087911454112739952835627)
    ·
      refine ⟨31631867181169109929253441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21087911454112739952835627 31631867181169109929253441)
      ·
        refine ⟨23723900385876832446940081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31631867181169109929253441 23723900385876832446940081)
        ·
          refine ⟨17792925289407624335205061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23723900385876832446940081 17792925289407624335205061)
          ·
            refine ⟨3336173491763929562850949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17792925289407624335205061 3336173491763929562850949)
            ·
              refine ⟨625532529705736793034553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3336173491763929562850949 625532529705736793034553)
              ·
                refine ⟨469149397279302594775915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625532529705736793034553 469149397279302594775915)
                ·
                  refine ⟨703724095918953892163873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469149397279302594775915 703724095918953892163873)
                  ·
                    refine ⟨527793071939215419122905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703724095918953892163873 527793071939215419122905)
                    ·
                      refine ⟨395844803954411564342179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527793071939215419122905 395844803954411564342179)
                      ·
                        rfl

theorem cell23_770905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_770905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770905 prefixEnd_770905 := by exact prefixLift 770905
  have htrace : WordTrace (prefixWord ++ tailWord_770905) baseStart_770905 baseEnd_770905 := by
    simpa [prefixWord, tailWord_770905, baseEnd_770905] using wordTrace_append hprefix tailTrace_770905
  have hstable : (prefixWord ++ tailWord_770905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770905).length < 2 ^ (prefixWord ++ tailWord_770905).sum := by decide
  have hdescent : baseEnd_770905 < baseStart_770905 := by decide
  rcases family_descends (prefixWord ++ tailWord_770905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770942 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_770942 : Nat := 118140960795 + 770942 * 2 ^ 59
def prefixEnd_770942 : Nat := 4983230072969 + 3 ^ 40 * 770942 * 2
def baseEnd_770942 : Nat := 395863802738627919579509

theorem tailTrace_770942 : CollatzResearch.WordTrace tailWord_770942 prefixEnd_770942 395863802738627919579509 := by
  unfold tailWord_770942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514820596627034407026385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18745709848677516837474053 3514820596627034407026385)
  ·
    refine ⟨2636115447470275805269789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3514820596627034407026385 2636115447470275805269789)
    ·
      refine ⟨988543292801353426976171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2636115447470275805269789 988543292801353426976171)
      ·
        refine ⟨1482814939202030140464257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988543292801353426976171 1482814939202030140464257)
        ·
          refine ⟨1112111204401522605348193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1482814939202030140464257 1112111204401522605348193)
          ·
            refine ⟨834083403301141954011145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112111204401522605348193 834083403301141954011145)
            ·
              refine ⟨625562552475856465508359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834083403301141954011145 625562552475856465508359)
              ·
                refine ⟨938343828713784698262539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625562552475856465508359 938343828713784698262539)
                ·
                  refine ⟨1407515743070677047393809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938343828713784698262539 1407515743070677047393809)
                  ·
                    refine ⟨1055636807303007785545357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1407515743070677047393809 1055636807303007785545357)
                    ·
                      refine ⟨395863802738627919579509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055636807303007785545357 395863802738627919579509)
                      ·
                        rfl

theorem cell23_770942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_770942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770942 prefixEnd_770942 := by exact prefixLift 770942
  have htrace : WordTrace (prefixWord ++ tailWord_770942) baseStart_770942 baseEnd_770942 := by
    simpa [prefixWord, tailWord_770942, baseEnd_770942] using wordTrace_append hprefix tailTrace_770942
  have hstable : (prefixWord ++ tailWord_770942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770942).length < 2 ^ (prefixWord ++ tailWord_770942).sum := by decide
  have hdescent : baseEnd_770942 < baseStart_770942 := by decide
  rcases family_descends (prefixWord ++ tailWord_770942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2]
def baseStart_770944 : Nat := 118140960795 + 770944 * 2 ^ 59
def prefixEnd_770944 : Nat := 4983230072969 + 3 ^ 40 * 770944 * 2
def baseEnd_770944 : Nat := 395864829699936911754499

theorem tailTrace_770944 : CollatzResearch.WordTrace tailWord_770944 prefixEnd_770944 395864829699936911754499 := by
  unfold tailWord_770944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14059318859504514798891943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18745758479339353065189257 14059318859504514798891943)
  ·
    refine ⟨21088978289256772198337915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14059318859504514798891943 21088978289256772198337915)
    ·
      refine ⟨31633467433885158297506873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21088978289256772198337915 31633467433885158297506873)
      ·
        refine ⟨23725100575413868723130155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31633467433885158297506873 23725100575413868723130155)
        ·
          refine ⟨35587650863120803084695233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23725100575413868723130155 35587650863120803084695233)
          ·
            refine ⟨26690738147340602313521425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35587650863120803084695233 26690738147340602313521425)
            ·
              refine ⟨20018053610505451735141069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26690738147340602313521425 20018053610505451735141069)
              ·
                refine ⟨7506770103939544400677901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20018053610505451735141069 7506770103939544400677901)
                ·
                  refine ⟨2815038788977329150254213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7506770103939544400677901 2815038788977329150254213)
                  ·
                    refine ⟨527819772933249215672665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815038788977329150254213 527819772933249215672665)
                    ·
                      refine ⟨395864829699936911754499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527819772933249215672665 395864829699936911754499)
                      ·
                        rfl

theorem cell23_770944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_770944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770944 prefixEnd_770944 := by exact prefixLift 770944
  have htrace : WordTrace (prefixWord ++ tailWord_770944) baseStart_770944 baseEnd_770944 := by
    simpa [prefixWord, tailWord_770944, baseEnd_770944] using wordTrace_append hprefix tailTrace_770944
  have hstable : (prefixWord ++ tailWord_770944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770944).length < 2 ^ (prefixWord ++ tailWord_770944).sum := by decide
  have hdescent : baseEnd_770944 < baseStart_770944 := by decide
  rcases family_descends (prefixWord ++ tailWord_770944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770947 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5]
def baseStart_770947 : Nat := 118140960795 + 770947 * 2 ^ 59
def prefixEnd_770947 : Nat := 4983230072969 + 3 ^ 40 * 770947 * 2
def baseEnd_770947 : Nat := 395866370141900400016985

theorem tailTrace_770947 : CollatzResearch.WordTrace tailWord_770947 prefixEnd_770947 395866370141900400016985 := by
  unfold tailWord_770947
  simp only [CollatzResearch.WordTrace]
  refine ⟨28118747137998161110143095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18745831425332107406762063 28118747137998161110143095)
  ·
    refine ⟨42178120706997241665214643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28118747137998161110143095 42178120706997241665214643)
    ·
      refine ⟨63267181060495862497821965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42178120706997241665214643 63267181060495862497821965)
      ·
        refine ⟨23725192897685948436683237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63267181060495862497821965 23725192897685948436683237)
        ·
          refine ⟨4448473668316115331878107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23725192897685948436683237 4448473668316115331878107)
          ·
            refine ⟨6672710502474172997817161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448473668316115331878107 6672710502474172997817161)
            ·
              refine ⟨5004532876855629748362871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6672710502474172997817161 5004532876855629748362871)
              ·
                refine ⟨7506799315283444622544307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004532876855629748362871 7506799315283444622544307)
                ·
                  refine ⟨11260198972925166933816461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7506799315283444622544307 11260198972925166933816461)
                  ·
                    refine ⟨4222574614846937600181173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11260198972925166933816461 4222574614846937600181173)
                    ·
                      refine ⟨395866370141900400016985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4222574614846937600181173 395866370141900400016985)
                      ·
                        rfl

theorem cell23_770947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_770947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770947 prefixEnd_770947 := by exact prefixLift 770947
  have htrace : WordTrace (prefixWord ++ tailWord_770947) baseStart_770947 baseEnd_770947 := by
    simpa [prefixWord, tailWord_770947, baseEnd_770947] using wordTrace_append hprefix tailTrace_770947
  have hstable : (prefixWord ++ tailWord_770947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770947).length < 2 ^ (prefixWord ++ tailWord_770947).sum := by decide
  have hdescent : baseEnd_770947 < baseStart_770947 := by decide
  rcases family_descends (prefixWord ++ tailWord_770947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770954 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 2, 6]
def baseStart_770954 : Nat := 118140960795 + 770954 * 2 ^ 59
def prefixEnd_770954 : Nat := 4983230072969 + 3 ^ 40 * 770954 * 2
def baseEnd_770954 : Nat := 131956654835493957543151

theorem tailTrace_770954 : CollatzResearch.WordTrace tailWord_770954 prefixEnd_770954 131956654835493957543151 := by
  unfold tailWord_770954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029750612243200326411979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18746001632648534203765277 7029750612243200326411979)
  ·
    refine ⟨10544625918364800489617969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029750612243200326411979 10544625918364800489617969)
    ·
      refine ⟨7908469438773600367213477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10544625918364800489617969 7908469438773600367213477)
      ·
        refine ⟨1482838019770050068852527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7908469438773600367213477 1482838019770050068852527)
        ·
          refine ⟨2224257029655075103278791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482838019770050068852527 2224257029655075103278791)
          ·
            refine ⟨3336385544482612654918187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224257029655075103278791 3336385544482612654918187)
            ·
              refine ⟨5004578316723918982377281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336385544482612654918187 5004578316723918982377281)
              ·
                refine ⟨3753433737542939236782961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004578316723918982377281 3753433737542939236782961)
                ·
                  refine ⟨2815075303157204427587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3753433737542939236782961 2815075303157204427587221)
                  ·
                    refine ⟨131956654835493957543151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2815075303157204427587221 131956654835493957543151)
                    ·
                      rfl

theorem cell23_770954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_770954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770954 prefixEnd_770954 := by exact prefixLift 770954
  have htrace : WordTrace (prefixWord ++ tailWord_770954) baseStart_770954 baseEnd_770954 := by
    simpa [prefixWord, tailWord_770954, baseEnd_770954] using wordTrace_append hprefix tailTrace_770954
  have hstable : (prefixWord ++ tailWord_770954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770954).length < 2 ^ (prefixWord ++ tailWord_770954).sum := by decide
  have hdescent : baseEnd_770954 < baseStart_770954 := by decide
  rcases family_descends (prefixWord ++ tailWord_770954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_770978 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_770978 : Nat := 118140960795 + 770978 * 2 ^ 59
def prefixEnd_770978 : Nat := 4983230072969 + 3 ^ 40 * 770978 * 2
def baseEnd_770978 : Nat := 395882288042189778729343

theorem tailTrace_770978 : CollatzResearch.WordTrace tailWord_770978 prefixEnd_770978 395882288042189778729343 := by
  unfold tailWord_770978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029969450221463351130397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18746585200590568936347725 7029969450221463351130397)
  ·
    refine ⟨2636238543833048756673899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7029969450221463351130397 2636238543833048756673899)
    ·
      refine ⟨3954357815749573135010849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636238543833048756673899 3954357815749573135010849)
      ·
        refine ⟨2965768361812179851258137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3954357815749573135010849 2965768361812179851258137)
        ·
          refine ⟨2224326271359134888443603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2965768361812179851258137 2224326271359134888443603)
          ·
            refine ⟨3336489407038702332665405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224326271359134888443603 3336489407038702332665405)
            ·
              refine ⟨1251183527639513374749527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336489407038702332665405 1251183527639513374749527)
              ·
                refine ⟨1876775291459270062124291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251183527639513374749527 1876775291459270062124291)
                ·
                  refine ⟨2815162937188905093186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876775291459270062124291 2815162937188905093186437)
                  ·
                    refine ⟨527843050722919704972457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815162937188905093186437 527843050722919704972457)
                    ·
                      refine ⟨395882288042189778729343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527843050722919704972457 395882288042189778729343)
                      ·
                        rfl

theorem cell23_770978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_770978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_770978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_770978 prefixEnd_770978 := by exact prefixLift 770978
  have htrace : WordTrace (prefixWord ++ tailWord_770978) baseStart_770978 baseEnd_770978 := by
    simpa [prefixWord, tailWord_770978, baseEnd_770978] using wordTrace_append hprefix tailTrace_770978
  have hstable : (prefixWord ++ tailWord_770978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_770978).length < 2 ^ (prefixWord ++ tailWord_770978).sum := by decide
  have hdescent : baseEnd_770978 < baseStart_770978 := by decide
  rcases family_descends (prefixWord ++ tailWord_770978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771001 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 5]
def baseStart_771001 : Nat := 118140960795 + 771001 * 2 ^ 59
def prefixEnd_771001 : Nat := 4983230072969 + 3 ^ 40 * 771001 * 2
def baseEnd_771001 : Nat := 43988233121915909860193

theorem tailTrace_771001 : CollatzResearch.WordTrace tailWord_771001 prefixEnd_771001 43988233121915909860193 := by
  unfold tailWord_771001
  simp only [CollatzResearch.WordTrace]
  refine ⟨28120716679802528332608857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18747144453201685555072571 28120716679802528332608857)
  ·
    refine ⟨21090537509851896249456643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28120716679802528332608857 21090537509851896249456643)
    ·
      refine ⟨31635806264777844374184965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21090537509851896249456643 31635806264777844374184965)
      ·
        refine ⟨5931713674645845820159681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31635806264777844374184965 5931713674645845820159681)
        ·
          refine ⟨4448785255984384365119761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5931713674645845820159681 4448785255984384365119761)
          ·
            refine ⟨3336588941988288273839821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448785255984384365119761 3336588941988288273839821)
            ·
              refine ⟨1251220853245608102689933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3336588941988288273839821 1251220853245608102689933)
              ·
                refine ⟨469207819967103038508725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1251220853245608102689933 469207819967103038508725)
                ·
                  refine ⟨43988233121915909860193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 469207819967103038508725 43988233121915909860193)
                  ·
                    rfl

theorem cell23_771001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 5].length) (baseStart_771001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771001 prefixEnd_771001 := by exact prefixLift 771001
  have htrace : WordTrace (prefixWord ++ tailWord_771001) baseStart_771001 baseEnd_771001 := by
    simpa [prefixWord, tailWord_771001, baseEnd_771001] using wordTrace_append hprefix tailTrace_771001
  have hstable : (prefixWord ++ tailWord_771001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771001).length < 2 ^ (prefixWord ++ tailWord_771001).sum := by decide
  have hdescent : baseEnd_771001 < baseStart_771001 := by decide
  rcases family_descends (prefixWord ++ tailWord_771001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771029 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 2, 2, 2]
def baseStart_771029 : Nat := 118140960795 + 771029 * 2 ^ 59
def prefixEnd_771029 : Nat := 4983230072969 + 3 ^ 40 * 771029 * 2
def baseEnd_771029 : Nat := 395908475555569079191609

theorem tailTrace_771029 : CollatzResearch.WordTrace tailWord_771029 prefixEnd_771029 395908475555569079191609 := by
  unfold tailWord_771029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28121737923701089114628141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18747825282467392743085427 28121737923701089114628141)
  ·
    refine ⟨10545651721387908417985553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28121737923701089114628141 10545651721387908417985553)
    ·
      refine ⟨7909238791040931313489165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10545651721387908417985553 7909238791040931313489165)
      ·
        refine ⟨2965964546640349242558437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7909238791040931313489165 2965964546640349242558437)
        ·
          refine ⟨556118352495065482979707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2965964546640349242558437 556118352495065482979707)
          ·
            refine ⟨834177528742598224469561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556118352495065482979707 834177528742598224469561)
            ·
              refine ⟨625633146556948668352171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834177528742598224469561 625633146556948668352171)
              ·
                refine ⟨938449719835423002528257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625633146556948668352171 938449719835423002528257)
                ·
                  refine ⟨703837289876567251896193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938449719835423002528257 703837289876567251896193)
                  ·
                    refine ⟨527877967407425438922145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 703837289876567251896193 527877967407425438922145)
                    ·
                      refine ⟨395908475555569079191609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 527877967407425438922145 395908475555569079191609)
                      ·
                        rfl

theorem cell23_771029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_771029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771029 prefixEnd_771029 := by exact prefixLift 771029
  have htrace : WordTrace (prefixWord ++ tailWord_771029) baseStart_771029 baseEnd_771029 := by
    simpa [prefixWord, tailWord_771029, baseEnd_771029] using wordTrace_append hprefix tailTrace_771029
  have hstable : (prefixWord ++ tailWord_771029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771029).length < 2 ^ (prefixWord ++ tailWord_771029).sum := by decide
  have hdescent : baseEnd_771029 < baseStart_771029 := by decide
  rcases family_descends (prefixWord ++ tailWord_771029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771118 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_771118 : Nat := 118140960795 + 771118 * 2 ^ 59
def prefixEnd_771118 : Nat := 4983230072969 + 3 ^ 40 * 771118 * 2
def baseEnd_771118 : Nat := 395954175333819230978699

theorem tailTrace_771118 : CollatzResearch.WordTrace tailWord_771118 prefixEnd_771118 395954175333819230978699 := by
  unfold tailWord_771118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515623002547332164327251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18749989346919104876412005 3515623002547332164327251)
  ·
    refine ⟨5273434503820998246490877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515623002547332164327251 5273434503820998246490877)
    ·
      refine ⟨1977537938932874342434079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5273434503820998246490877 1977537938932874342434079)
      ·
        refine ⟨2966306908399311513651119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977537938932874342434079 2966306908399311513651119)
        ·
          refine ⟨4449460362598967270476679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966306908399311513651119 4449460362598967270476679)
          ·
            refine ⟨6674190543898450905715019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449460362598967270476679 6674190543898450905715019)
            ·
              refine ⟨10011285815847676358572529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674190543898450905715019 10011285815847676358572529)
              ·
                refine ⟨7508464361885757268929397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10011285815847676358572529 7508464361885757268929397)
                ·
                  refine ⟨703918533926789743962131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7508464361885757268929397 703918533926789743962131)
                  ·
                    refine ⟨1055877800890184615943197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 703918533926789743962131 1055877800890184615943197)
                    ·
                      refine ⟨395954175333819230978699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1055877800890184615943197 395954175333819230978699)
                      ·
                        rfl

theorem cell23_771118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_771118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771118 prefixEnd_771118 := by exact prefixLift 771118
  have htrace : WordTrace (prefixWord ++ tailWord_771118) baseStart_771118 baseEnd_771118 := by
    simpa [prefixWord, tailWord_771118, baseEnd_771118] using wordTrace_append hprefix tailTrace_771118
  have hstable : (prefixWord ++ tailWord_771118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771118).length < 2 ^ (prefixWord ++ tailWord_771118).sum := by decide
  have hdescent : baseEnd_771118 < baseStart_771118 := by decide
  rcases family_descends (prefixWord ++ tailWord_771118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771121 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 1, 5]
def baseStart_771121 : Nat := 118140960795 + 771121 * 2 ^ 59
def prefixEnd_771121 : Nat := 4983230072969 + 3 ^ 40 * 771121 * 2
def baseEnd_771121 : Nat := 131985238591927573080395

theorem tailTrace_771121 : CollatzResearch.WordTrace tailWord_771121 prefixEnd_771121 131985238591927573080395 := by
  unfold tailWord_771121
  simp only [CollatzResearch.WordTrace]
  refine ⟨28125093439367788826977217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18750062292911859217984811 28125093439367788826977217)
  ·
    refine ⟨21093820079525841620232913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28125093439367788826977217 21093820079525841620232913)
    ·
      refine ⟨15820365059644381215174685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21093820079525841620232913 15820365059644381215174685)
      ·
        refine ⟨5932636897366642955690507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15820365059644381215174685 5932636897366642955690507)
        ·
          refine ⟨8898955346049964433535761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932636897366642955690507 8898955346049964433535761)
          ·
            refine ⟨6674216509537473325151821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8898955346049964433535761 6674216509537473325151821)
            ·
              refine ⟨2502831191076552496931933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6674216509537473325151821 2502831191076552496931933)
              ·
                refine ⟨938561696653707186349475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2502831191076552496931933 938561696653707186349475)
                ·
                  refine ⟨1407842544980560779524213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938561696653707186349475 1407842544980560779524213)
                  ·
                    refine ⟨131985238591927573080395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1407842544980560779524213 131985238591927573080395)
                    ·
                      rfl

theorem cell23_771121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_771121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771121 prefixEnd_771121 := by exact prefixLift 771121
  have htrace : WordTrace (prefixWord ++ tailWord_771121) baseStart_771121 baseEnd_771121 := by
    simpa [prefixWord, tailWord_771121, baseEnd_771121] using wordTrace_append hprefix tailTrace_771121
  have hstable : (prefixWord ++ tailWord_771121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771121).length < 2 ^ (prefixWord ++ tailWord_771121).sum := by decide
  have hdescent : baseEnd_771121 < baseStart_771121 := by decide
  rcases family_descends (prefixWord ++ tailWord_771121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771178 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_771178 : Nat := 118140960795 + 771178 * 2 ^ 59
def prefixEnd_771178 : Nat := 4983230072969 + 3 ^ 40 * 771178 * 2
def baseEnd_771178 : Nat := 395984984173088996228423

theorem tailTrace_771178 : CollatzResearch.WordTrace tailWord_771178 prefixEnd_771178 395984984173088996228423 := by
  unfold tailWord_771178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031793100040321890450547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18751448266774191707868125 7031793100040321890450547)
  ·
    refine ⟨10547689650060482835675821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031793100040321890450547 10547689650060482835675821)
    ·
      refine ⟨3955383618772681063378433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10547689650060482835675821 3955383618772681063378433)
      ·
        refine ⟨2966537714079510797533825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3955383618772681063378433 2966537714079510797533825)
        ·
          refine ⟨2224903285559633098150369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2966537714079510797533825 2224903285559633098150369)
          ·
            refine ⟨1668677464169724823612777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224903285559633098150369 1668677464169724823612777)
            ·
              refine ⟨1251508098127293617709583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668677464169724823612777 1251508098127293617709583)
              ·
                refine ⟨1877262147190940426564375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251508098127293617709583 1877262147190940426564375)
                ·
                  refine ⟨2815893220786410639846563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877262147190940426564375 2815893220786410639846563)
                  ·
                    refine ⟨4223839831179615959769845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2815893220786410639846563 4223839831179615959769845)
                    ·
                      refine ⟨395984984173088996228423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4223839831179615959769845 395984984173088996228423)
                      ·
                        rfl

theorem cell23_771178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_771178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771178 prefixEnd_771178 := by exact prefixLift 771178
  have htrace : WordTrace (prefixWord ++ tailWord_771178) baseStart_771178 baseEnd_771178 := by
    simpa [prefixWord, tailWord_771178, baseEnd_771178] using wordTrace_append hprefix tailTrace_771178
  have hstable : (prefixWord ++ tailWord_771178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771178).length < 2 ^ (prefixWord ++ tailWord_771178).sum := by decide
  have hdescent : baseEnd_771178 < baseStart_771178 := by decide
  rcases family_descends (prefixWord ++ tailWord_771178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771181 : List Nat := [1, 5, 1, 1, 2, 4, 9]
def baseStart_771181 : Nat := 118140960795 + 771181 * 2 ^ 59
def prefixEnd_771181 : Nat := 4983230072969 + 3 ^ 40 * 771181 * 2
def baseEnd_771181 : Nat := 4888722526111759067789

theorem tailTrace_771181 : CollatzResearch.WordTrace tailWord_771181 prefixEnd_771181 4888722526111759067789 := by
  unfold tailWord_771181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28127281819150419074161397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18751521212766946049440931 28127281819150419074161397)
  ·
    refine ⟨2636932670545351788202631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28127281819150419074161397 2636932670545351788202631)
    ·
      refine ⟨3955399005818027682303947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2636932670545351788202631 3955399005818027682303947)
      ·
        refine ⟨5933098508727041523455921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3955399005818027682303947 5933098508727041523455921)
        ·
          refine ⟨4449823881545281142591941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5933098508727041523455921 4449823881545281142591941)
          ·
            refine ⟨834341977789740214235989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4449823881545281142591941 834341977789740214235989)
            ·
              refine ⟨4888722526111759067789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 834341977789740214235989 4888722526111759067789)
              ·
                rfl

theorem cell23_771181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 9].length) (baseStart_771181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771181 prefixEnd_771181 := by exact prefixLift 771181
  have htrace : WordTrace (prefixWord ++ tailWord_771181) baseStart_771181 baseEnd_771181 := by
    simpa [prefixWord, tailWord_771181, baseEnd_771181] using wordTrace_append hprefix tailTrace_771181
  have hstable : (prefixWord ++ tailWord_771181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771181).length < 2 ^ (prefixWord ++ tailWord_771181).sum := by decide
  have hdescent : baseEnd_771181 < baseStart_771181 := by decide
  rcases family_descends (prefixWord ++ tailWord_771181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771242 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_771242 : Nat := 118140960795 + 771242 * 2 ^ 59
def prefixEnd_771242 : Nat := 4983230072969 + 3 ^ 40 * 771242 * 2
def baseEnd_771242 : Nat := 396017846934976745828129

theorem tailTrace_771242 : CollatzResearch.WordTrace tailWord_771242 prefixEnd_771242 396017846934976745828129 := by
  unfold tailWord_771242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032376667982356623032995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18753004447952950994754653 7032376667982356623032995)
  ·
    refine ⟨10548565001973534934549493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7032376667982356623032995 10548565001973534934549493)
    ·
      refine ⟨988927968935018900114015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10548565001973534934549493 988927968935018900114015)
      ·
        refine ⟨1483391953402528350171023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 988927968935018900114015 1483391953402528350171023)
        ·
          refine ⟨2225087930103792525256535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483391953402528350171023 2225087930103792525256535)
          ·
            refine ⟨3337631895155688787884803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225087930103792525256535 3337631895155688787884803)
            ·
              refine ⟨5006447842733533181827205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337631895155688787884803 5006447842733533181827205)
              ·
                refine ⟨938708970512537471592601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5006447842733533181827205 938708970512537471592601)
                ·
                  refine ⟨704031727884403103694451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 938708970512537471592601 704031727884403103694451)
                  ·
                    refine ⟨1056047591826604655541677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704031727884403103694451 1056047591826604655541677)
                    ·
                      refine ⟨396017846934976745828129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056047591826604655541677 396017846934976745828129)
                      ·
                        rfl

theorem cell23_771242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_771242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771242 prefixEnd_771242 := by exact prefixLift 771242
  have htrace : WordTrace (prefixWord ++ tailWord_771242) baseStart_771242 baseEnd_771242 := by
    simpa [prefixWord, tailWord_771242, baseEnd_771242] using wordTrace_append hprefix tailTrace_771242
  have hstable : (prefixWord ++ tailWord_771242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771242).length < 2 ^ (prefixWord ++ tailWord_771242).sum := by decide
  have hdescent : baseEnd_771242 < baseStart_771242 := by decide
  rcases family_descends (prefixWord ++ tailWord_771242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771251 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3]
def baseStart_771251 : Nat := 118140960795 + 771251 * 2 ^ 59
def prefixEnd_771251 : Nat := 4983230072969 + 3 ^ 40 * 771251 * 2
def baseEnd_771251 : Nat := 396022468260867210615587

theorem tailTrace_771251 : CollatzResearch.WordTrace tailWord_771251 prefixEnd_771251 396022468260867210615587 := by
  unfold tailWord_771251
  simp only [CollatzResearch.WordTrace]
  refine ⟨28129834928896821029209607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18753223285931214019473071 28129834928896821029209607)
  ·
    refine ⟨42194752393345231543814411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28129834928896821029209607 42194752393345231543814411)
    ·
      refine ⟨63292128590017847315721617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42194752393345231543814411 63292128590017847315721617)
      ·
        refine ⟨47469096442513385486791213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63292128590017847315721617 47469096442513385486791213)
        ·
          refine ⟨17800911165942519557546705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47469096442513385486791213 17800911165942519557546705)
          ·
            refine ⟨13350683374456889668160029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17800911165942519557546705 13350683374456889668160029)
            ·
              refine ⟨5006506265421333625560011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13350683374456889668160029 5006506265421333625560011)
              ·
                refine ⟨7509759398132000438340017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006506265421333625560011 7509759398132000438340017)
                ·
                  refine ⟨5632319548599000328755013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7509759398132000438340017 5632319548599000328755013)
                  ·
                    refine ⟨1056059915362312561641565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5632319548599000328755013 1056059915362312561641565)
                    ·
                      refine ⟨396022468260867210615587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056059915362312561641565 396022468260867210615587)
                      ·
                        rfl

theorem cell23_771251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_771251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771251 prefixEnd_771251 := by exact prefixLift 771251
  have htrace : WordTrace (prefixWord ++ tailWord_771251) baseStart_771251 baseEnd_771251 := by
    simpa [prefixWord, tailWord_771251, baseEnd_771251] using wordTrace_append hprefix tailTrace_771251
  have hstable : (prefixWord ++ tailWord_771251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771251).length < 2 ^ (prefixWord ++ tailWord_771251).sum := by decide
  have hdescent : baseEnd_771251 < baseStart_771251 := by decide
  rcases family_descends (prefixWord ++ tailWord_771251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771261 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 4]
def baseStart_771261 : Nat := 118140960795 + 771261 * 2 ^ 59
def prefixEnd_771261 : Nat := 4983230072969 + 3 ^ 40 * 771261 * 2
def baseEnd_771261 : Nat := 396027603067412171490541

theorem tailTrace_771261 : CollatzResearch.WordTrace tailWord_771261 prefixEnd_771261 396027603067412171490541 := by
  unfold tailWord_771261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130199658860592737073637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18753466439240395158049091 28130199658860592737073637)
  ·
    refine ⟨5274412436036361138201307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28130199658860592737073637 5274412436036361138201307)
    ·
      refine ⟨7911618654054541707301961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5274412436036361138201307 7911618654054541707301961)
      ·
        refine ⟨5933713990540906280476471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7911618654054541707301961 5933713990540906280476471)
        ·
          refine ⟨8900570985811359420714707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933713990540906280476471 8900570985811359420714707)
          ·
            refine ⟨13350856478717039131072061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900570985811359420714707 13350856478717039131072061)
            ·
              refine ⟨5006571179518889674152023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13350856478717039131072061 5006571179518889674152023)
              ·
                refine ⟨7509856769278334511228035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5006571179518889674152023 7509856769278334511228035)
                ·
                  refine ⟨11264785153917501766842053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7509856769278334511228035 11264785153917501766842053)
                  ·
                    refine ⟨2112147216359531581282885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11264785153917501766842053 2112147216359531581282885)
                    ·
                      refine ⟨396027603067412171490541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2112147216359531581282885 396027603067412171490541)
                      ·
                        rfl

theorem cell23_771261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_771261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771261 prefixEnd_771261 := by exact prefixLift 771261
  have htrace : WordTrace (prefixWord ++ tailWord_771261) baseStart_771261 baseEnd_771261 := by
    simpa [prefixWord, tailWord_771261, baseEnd_771261] using wordTrace_append hprefix tailTrace_771261
  have hstable : (prefixWord ++ tailWord_771261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771261).length < 2 ^ (prefixWord ++ tailWord_771261).sum := by decide
  have hdescent : baseEnd_771261 < baseStart_771261 := by decide
  rcases family_descends (prefixWord ++ tailWord_771261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771281 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_771281 : Nat := 118140960795 + 771281 * 2 ^ 59
def prefixEnd_771281 : Nat := 4983230072969 + 3 ^ 40 * 771281 * 2
def baseEnd_771281 : Nat := 396037872680502093240449

theorem tailTrace_771281 : CollatzResearch.WordTrace tailWord_771281 prefixEnd_771281 396037872680502093240449 := by
  unfold tailWord_771281
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130929118788136152801697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18753952745858757435201131 28130929118788136152801697)
  ·
    refine ⟨21098196839091102114601273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28130929118788136152801697 21098196839091102114601273)
    ·
      refine ⟨15823647629318326585950955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21098196839091102114601273 15823647629318326585950955)
      ·
        refine ⟨23735471443977489878926433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15823647629318326585950955 23735471443977489878926433)
        ·
          refine ⟨17801603582983117409194825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23735471443977489878926433 17801603582983117409194825)
          ·
            refine ⟨13351202687237338056896119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17801603582983117409194825 13351202687237338056896119)
            ·
              refine ⟨20026804030856007085344179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13351202687237338056896119 20026804030856007085344179)
              ·
                refine ⟨30040206046284010628016269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20026804030856007085344179 30040206046284010628016269)
                ·
                  refine ⟨11265077267356503985506101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30040206046284010628016269 11265077267356503985506101)
                  ·
                    refine ⟨1056100993814672248641197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11265077267356503985506101 1056100993814672248641197)
                    ·
                      refine ⟨396037872680502093240449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056100993814672248641197 396037872680502093240449)
                      ·
                        rfl

theorem cell23_771281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_771281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771281 prefixEnd_771281 := by exact prefixLift 771281
  have htrace : WordTrace (prefixWord ++ tailWord_771281) baseStart_771281 baseEnd_771281 := by
    simpa [prefixWord, tailWord_771281, baseEnd_771281] using wordTrace_append hprefix tailTrace_771281
  have hstable : (prefixWord ++ tailWord_771281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771281).length < 2 ^ (prefixWord ++ tailWord_771281).sum := by decide
  have hdescent : baseEnd_771281 < baseStart_771281 := by decide
  rcases family_descends (prefixWord ++ tailWord_771281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771321 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_771321 : Nat := 118140960795 + 771321 * 2 ^ 59
def prefixEnd_771321 : Nat := 4983230072969 + 3 ^ 40 * 771321 * 2
def baseEnd_771321 : Nat := 396058411906681936740265

theorem tailTrace_771321 : CollatzResearch.WordTrace tailWord_771321 prefixEnd_771321 396058411906681936740265 := by
  unfold tailWord_771321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28132388038643222984257817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18754925359095481989505211 28132388038643222984257817)
  ·
    refine ⟨21099291028982417238193363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28132388038643222984257817 21099291028982417238193363)
    ·
      refine ⟨31648936543473625857290045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21099291028982417238193363 31648936543473625857290045)
      ·
        refine ⟨11868351203802609696483767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31648936543473625857290045 11868351203802609696483767)
        ·
          refine ⟨17802526805703914544725651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11868351203802609696483767 17802526805703914544725651)
          ·
            refine ⟨26703790208555871817088477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17802526805703914544725651 26703790208555871817088477)
            ·
              refine ⟨10013921328208451931408179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26703790208555871817088477 10013921328208451931408179)
              ·
                refine ⟨15020881992312677897112269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10013921328208451931408179 15020881992312677897112269)
                ·
                  refine ⟨5632830747117254211417101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15020881992312677897112269 5632830747117254211417101)
                  ·
                    refine ⟨2112311530168970329281413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5632830747117254211417101 2112311530168970329281413)
                    ·
                      refine ⟨396058411906681936740265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2112311530168970329281413 396058411906681936740265)
                      ·
                        rfl

theorem cell23_771321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_771321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771321 prefixEnd_771321 := by exact prefixLift 771321
  have htrace : WordTrace (prefixWord ++ tailWord_771321) baseStart_771321 baseEnd_771321 := by
    simpa [prefixWord, tailWord_771321, baseEnd_771321] using wordTrace_append hprefix tailTrace_771321
  have hstable : (prefixWord ++ tailWord_771321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771321).length < 2 ^ (prefixWord ++ tailWord_771321).sum := by decide
  have hdescent : baseEnd_771321 < baseStart_771321 := by decide
  rcases family_descends (prefixWord ++ tailWord_771321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771338 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_771338 : Nat := 118140960795 + 771338 * 2 ^ 59
def prefixEnd_771338 : Nat := 4983230072969 + 3 ^ 40 * 771338 * 2
def baseEnd_771338 : Nat := 396067141077808370227687

theorem tailTrace_771338 : CollatzResearch.WordTrace tailWord_771338 prefixEnd_771338 396067141077808370227687 := by
  unfold tailWord_771338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033252019895408721906667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18755338719721089925084445 7033252019895408721906667)
  ·
    refine ⟨10549878029843113082860001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7033252019895408721906667 10549878029843113082860001)
    ·
      refine ⟨7912408522382334812145001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10549878029843113082860001 7912408522382334812145001)
      ·
        refine ⟨5934306391786751109108751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7912408522382334812145001 5934306391786751109108751)
        ·
          refine ⟨8901459587680126663663127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5934306391786751109108751 8901459587680126663663127)
          ·
            refine ⟨13352189381520189995494691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8901459587680126663663127 13352189381520189995494691)
            ·
              refine ⟨20028284072280284993242037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13352189381520189995494691 20028284072280284993242037)
              ·
                refine ⟨1877651631776276718116441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20028284072280284993242037 1877651631776276718116441)
                ·
                  refine ⟨1408238723832207538587331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877651631776276718116441 1408238723832207538587331)
                  ·
                    refine ⟨2112358085748311307880997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1408238723832207538587331 2112358085748311307880997)
                    ·
                      refine ⟨396067141077808370227687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2112358085748311307880997 396067141077808370227687)
                      ·
                        rfl

theorem cell23_771338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_771338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771338 prefixEnd_771338 := by exact prefixLift 771338
  have htrace : WordTrace (prefixWord ++ tailWord_771338) baseStart_771338 baseEnd_771338 := by
    simpa [prefixWord, tailWord_771338, baseEnd_771338] using wordTrace_append hprefix tailTrace_771338
  have hstable : (prefixWord ++ tailWord_771338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771338).length < 2 ^ (prefixWord ++ tailWord_771338).sum := by decide
  have hdescent : baseEnd_771338 < baseStart_771338 := by decide
  rcases family_descends (prefixWord ++ tailWord_771338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771365 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_771365 : Nat := 118140960795 + 771365 * 2 ^ 59
def prefixEnd_771365 : Nat := 4983230072969 + 3 ^ 40 * 771365 * 2
def baseEnd_771365 : Nat := 132027001685159921530021

theorem tailTrace_771365 : CollatzResearch.WordTrace tailWord_771365 prefixEnd_771365 132027001685159921530021 := by
  unfold tailWord_771365
  simp only [CollatzResearch.WordTrace]
  refine ⟨28133992850483818498859549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18755995233655878999239699 28133992850483818498859549)
  ·
    refine ⟨10550247318931431937072331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28133992850483818498859549 10550247318931431937072331)
    ·
      refine ⟨15825370978397147905608497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10550247318931431937072331 15825370978397147905608497)
      ·
        refine ⟨11869028233797860929206373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15825370978397147905608497 11869028233797860929206373)
        ·
          refine ⟨2225442793837098924226195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11869028233797860929206373 2225442793837098924226195)
          ·
            refine ⟨3338164190755648386339293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225442793837098924226195 3338164190755648386339293)
            ·
              refine ⟨1251811571533368144877235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3338164190755648386339293 1251811571533368144877235)
              ·
                refine ⟨1877717357300052217315853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251811571533368144877235 1877717357300052217315853)
                ·
                  refine ⟨704144008987519581493445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1877717357300052217315853 704144008987519581493445)
                  ·
                    refine ⟨132027001685159921530021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704144008987519581493445 132027001685159921530021)
                    ·
                      rfl

theorem cell23_771365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_771365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771365 prefixEnd_771365 := by exact prefixLift 771365
  have htrace : WordTrace (prefixWord ++ tailWord_771365) baseStart_771365 baseEnd_771365 := by
    simpa [prefixWord, tailWord_771365, baseEnd_771365] using wordTrace_append hprefix tailTrace_771365
  have hstable : (prefixWord ++ tailWord_771365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771365).length < 2 ^ (prefixWord ++ tailWord_771365).sum := by decide
  have hdescent : baseEnd_771365 < baseStart_771365 := by decide
  rcases family_descends (prefixWord ++ tailWord_771365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771513 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 1, 2, 2]
def baseStart_771513 : Nat := 118140960795 + 771513 * 2 ^ 59
def prefixEnd_771513 : Nat := 4983230072969 + 3 ^ 40 * 771513 * 2
def baseEnd_771513 : Nat := 396157000192345185539383

theorem tailTrace_771513 : CollatzResearch.WordTrace tailWord_771513 prefixEnd_771513 396157000192345185539383 := by
  unfold tailWord_771513
  simp only [CollatzResearch.WordTrace]
  refine ⟨28139390853947639775247193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18759593902631759850164795 28139390853947639775247193)
  ·
    refine ⟨21104543140460729831435395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28139390853947639775247193 21104543140460729831435395)
    ·
      refine ⟨31656814710691094747153093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21104543140460729831435395 31656814710691094747153093)
      ·
        refine ⟨5935652758254580265091205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31656814710691094747153093 5935652758254580265091205)
        ·
          refine ⟨1112934892172733799704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5935652758254580265091205 1112934892172733799704601)
          ·
            refine ⟨834701169129550349778451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1112934892172733799704601 834701169129550349778451)
            ·
              refine ⟨1252051753694325524667677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 834701169129550349778451 1252051753694325524667677)
              ·
                refine ⟨469519407635372071750379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252051753694325524667677 469519407635372071750379)
                ·
                  refine ⟨704279111453058107625569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469519407635372071750379 704279111453058107625569)
                  ·
                    refine ⟨528209333589793580719177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 704279111453058107625569 528209333589793580719177)
                    ·
                      refine ⟨396157000192345185539383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528209333589793580719177 396157000192345185539383)
                      ·
                        rfl

theorem cell23_771513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_771513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771513 prefixEnd_771513 := by exact prefixLift 771513
  have htrace : WordTrace (prefixWord ++ tailWord_771513) baseStart_771513 baseEnd_771513 := by
    simpa [prefixWord, tailWord_771513, baseEnd_771513] using wordTrace_append hprefix tailTrace_771513
  have hstable : (prefixWord ++ tailWord_771513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771513).length < 2 ^ (prefixWord ++ tailWord_771513).sum := by decide
  have hdescent : baseEnd_771513 < baseStart_771513 := by decide
  rcases family_descends (prefixWord ++ tailWord_771513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771546 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3]
def baseStart_771546 : Nat := 118140960795 + 771546 * 2 ^ 59
def prefixEnd_771546 : Nat := 4983230072969 + 3 ^ 40 * 771546 * 2
def baseEnd_771546 : Nat := 396173945053943556426731

theorem tailTrace_771546 : CollatzResearch.WordTrace tailWord_771546 prefixEnd_771546 396173945053943556426731 := by
  unfold tailWord_771546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7035148615707021602799623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18760396308552057607465661 7035148615707021602799623)
  ·
    refine ⟨10552722923560532404199435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7035148615707021602799623 10552722923560532404199435)
    ·
      refine ⟨15829084385340798606299153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552722923560532404199435 15829084385340798606299153)
      ·
        refine ⟨11871813289005598954724365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15829084385340798606299153 11871813289005598954724365)
        ·
          refine ⟨4451929983377099608021637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11871813289005598954724365 4451929983377099608021637)
          ·
            refine ⟨834736871883206176504057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4451929983377099608021637 834736871883206176504057)
            ·
              refine ⟨626052653912404632378043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834736871883206176504057 626052653912404632378043)
              ·
                refine ⟨939078980868606948567065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626052653912404632378043 939078980868606948567065)
                ·
                  refine ⟨704309235651455211425299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939078980868606948567065 704309235651455211425299)
                  ·
                    refine ⟨1056463853477182817137949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704309235651455211425299 1056463853477182817137949)
                    ·
                      refine ⟨396173945053943556426731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056463853477182817137949 396173945053943556426731)
                      ·
                        rfl

theorem cell23_771546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3].length) (baseStart_771546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771546 prefixEnd_771546 := by exact prefixLift 771546
  have htrace : WordTrace (prefixWord ++ tailWord_771546) baseStart_771546 baseEnd_771546 := by
    simpa [prefixWord, tailWord_771546, baseEnd_771546] using wordTrace_append hprefix tailTrace_771546
  have hstable : (prefixWord ++ tailWord_771546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771546).length < 2 ^ (prefixWord ++ tailWord_771546).sum := by decide
  have hdescent : baseEnd_771546 < baseStart_771546 := by decide
  rcases family_descends (prefixWord ++ tailWord_771546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771552 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2]
def baseStart_771552 : Nat := 118140960795 + 771552 * 2 ^ 59
def prefixEnd_771552 : Nat := 4983230072969 + 3 ^ 40 * 771552 * 2
def baseEnd_771552 : Nat := 396177025937870532951703

theorem tailTrace_771552 : CollatzResearch.WordTrace tailWord_771552 prefixEnd_771552 396177025937870532951703 := by
  unfold tailWord_771552
  simp only [CollatzResearch.WordTrace]
  refine ⟨14070406650403174717958455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18760542200537566290611273 14070406650403174717958455)
  ·
    refine ⟨21105609975604762076937683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14070406650403174717958455 21105609975604762076937683)
    ·
      refine ⟨31658414963407143115406525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21105609975604762076937683 31658414963407143115406525)
      ·
        refine ⟨11871905611277678668277447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31658414963407143115406525 11871905611277678668277447)
        ·
          refine ⟨17807858416916518002416171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11871905611277678668277447 17807858416916518002416171)
          ·
            refine ⟨26711787625374777003624257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17807858416916518002416171 26711787625374777003624257)
            ·
              refine ⟨20033840719031082752718193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26711787625374777003624257 20033840719031082752718193)
              ·
                refine ⟨15025380539273312064538645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20033840719031082752718193 15025380539273312064538645)
                ·
                  refine ⟨704314712778436503025249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15025380539273312064538645 704314712778436503025249)
                  ·
                    refine ⟨528236034583827377268937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 704314712778436503025249 528236034583827377268937)
                    ·
                      refine ⟨396177025937870532951703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528236034583827377268937 396177025937870532951703)
                      ·
                        rfl

theorem cell23_771552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_771552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771552 prefixEnd_771552 := by exact prefixLift 771552
  have htrace : WordTrace (prefixWord ++ tailWord_771552) baseStart_771552 baseEnd_771552 := by
    simpa [prefixWord, tailWord_771552, baseEnd_771552] using wordTrace_append hprefix tailTrace_771552
  have hstable : (prefixWord ++ tailWord_771552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771552).length < 2 ^ (prefixWord ++ tailWord_771552).sum := by decide
  have hdescent : baseEnd_771552 < baseStart_771552 := by decide
  rcases family_descends (prefixWord ++ tailWord_771552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771555 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5]
def baseStart_771555 : Nat := 118140960795 + 771555 * 2 ^ 59
def prefixEnd_771555 : Nat := 4983230072969 + 3 ^ 40 * 771555 * 2
def baseEnd_771555 : Nat := 396178566379834021214189

theorem tailTrace_771555 : CollatzResearch.WordTrace tailWord_771555 prefixEnd_771555 396178566379834021214189 := by
  unfold tailWord_771555
  simp only [CollatzResearch.WordTrace]
  refine ⟨28140922719795480948276119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18760615146530320632184079 28140922719795480948276119)
  ·
    refine ⟨42211384079693221422414179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28140922719795480948276119 42211384079693221422414179)
    ·
      refine ⟨63317076119539832133621269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42211384079693221422414179 63317076119539832133621269)
      ·
        refine ⟨2967987943103429631263497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63317076119539832133621269 2967987943103429631263497)
        ·
          refine ⟨2225990957327572223447623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2967987943103429631263497 2225990957327572223447623)
          ·
            refine ⟨3338986435991358335171435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225990957327572223447623 3338986435991358335171435)
            ·
              refine ⟨5008479653987037502757153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338986435991358335171435 5008479653987037502757153)
              ·
                refine ⟨3756359740490278127067865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5008479653987037502757153 3756359740490278127067865)
                ·
                  refine ⟨2817269805367708595300899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756359740490278127067865 2817269805367708595300899)
                  ·
                    refine ⟨4225904708051562892951349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2817269805367708595300899 4225904708051562892951349)
                    ·
                      refine ⟨396178566379834021214189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4225904708051562892951349 396178566379834021214189)
                      ·
                        rfl

theorem cell23_771555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_771555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771555 prefixEnd_771555 := by exact prefixLift 771555
  have htrace : WordTrace (prefixWord ++ tailWord_771555) baseStart_771555 baseEnd_771555 := by
    simpa [prefixWord, tailWord_771555, baseEnd_771555] using wordTrace_append hprefix tailTrace_771555
  have hstable : (prefixWord ++ tailWord_771555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771555).length < 2 ^ (prefixWord ++ tailWord_771555).sum := by decide
  have hdescent : baseEnd_771555 < baseStart_771555 := by decide
  rcases family_descends (prefixWord ++ tailWord_771555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771573 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_771573 : Nat := 118140960795 + 771573 * 2 ^ 59
def prefixEnd_771573 : Nat := 4983230072969 + 3 ^ 40 * 771573 * 2
def baseEnd_771573 : Nat := 396187809031614950789107

theorem tailTrace_771573 : CollatzResearch.WordTrace tailWord_771573 prefixEnd_771573 396187809031614950789107 := by
  unfold tailWord_771573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28141579233730270022431373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18761052822486846681620915 28141579233730270022431373)
  ·
    refine ⟨10553092212648851258411765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28141579233730270022431373 10553092212648851258411765)
    ·
      refine ⟨989352394935829805476103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10553092212648851258411765 989352394935829805476103)
      ·
        refine ⟨1484028592403744708214155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989352394935829805476103 1484028592403744708214155)
        ·
          refine ⟨2226042888605617062321233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484028592403744708214155 2226042888605617062321233)
          ·
            refine ⟨1669532166454212796740925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226042888605617062321233 1669532166454212796740925)
            ·
              refine ⟨626074562420329798777847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1669532166454212796740925 626074562420329798777847)
              ·
                refine ⟨939111843630494698166771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626074562420329798777847 939111843630494698166771)
                ·
                  refine ⟨1408667765445742047250157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939111843630494698166771 1408667765445742047250157)
                  ·
                    refine ⟨528250412042153267718809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408667765445742047250157 528250412042153267718809)
                    ·
                      refine ⟨396187809031614950789107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528250412042153267718809 396187809031614950789107)
                      ·
                        rfl

theorem cell23_771573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_771573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771573 prefixEnd_771573 := by exact prefixLift 771573
  have htrace : WordTrace (prefixWord ++ tailWord_771573) baseStart_771573 baseEnd_771573 := by
    simpa [prefixWord, tailWord_771573, baseEnd_771573] using wordTrace_append hprefix tailTrace_771573
  have hstable : (prefixWord ++ tailWord_771573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771573).length < 2 ^ (prefixWord ++ tailWord_771573).sum := by decide
  have hdescent : baseEnd_771573 < baseStart_771573 := by decide
  rcases family_descends (prefixWord ++ tailWord_771573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771612 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_771612 : Nat := 118140960795 + 771612 * 2 ^ 59
def prefixEnd_771612 : Nat := 4983230072969 + 3 ^ 40 * 771612 * 2
def baseEnd_771612 : Nat := 396207834777140298201427

theorem tailTrace_771612 : CollatzResearch.WordTrace tailWord_771612 prefixEnd_771612 396207834777140298201427 := by
  unfold tailWord_771612
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071500840294489841550545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18762001120392653122067393 14071500840294489841550545)
  ·
    refine ⟨10553625630220867381162909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14071500840294489841550545 10553625630220867381162909)
    ·
      refine ⟨3957609611332825267936091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10553625630220867381162909 3957609611332825267936091)
      ·
        refine ⟨5936414416999237901904137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957609611332825267936091 5936414416999237901904137)
        ·
          refine ⟨4452310812749428426428103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5936414416999237901904137 4452310812749428426428103)
          ·
            refine ⟨6678466219124142639642155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4452310812749428426428103 6678466219124142639642155)
            ·
              refine ⟨10017699328686213959463233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678466219124142639642155 10017699328686213959463233)
              ·
                refine ⟨7513274496514660469597425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10017699328686213959463233 7513274496514660469597425)
                ·
                  refine ⟨5634955872385995352198069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7513274496514660469597425 5634955872385995352198069)
                  ·
                    refine ⟨528277113036187064268569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5634955872385995352198069 528277113036187064268569)
                    ·
                      refine ⟨396207834777140298201427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528277113036187064268569 396207834777140298201427)
                      ·
                        rfl

theorem cell23_771612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_771612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771612 prefixEnd_771612 := by exact prefixLift 771612
  have htrace : WordTrace (prefixWord ++ tailWord_771612) baseStart_771612 baseEnd_771612 := by
    simpa [prefixWord, tailWord_771612, baseEnd_771612] using wordTrace_append hprefix tailTrace_771612
  have hstable : (prefixWord ++ tailWord_771612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771612).length < 2 ^ (prefixWord ++ tailWord_771612).sum := by decide
  have hdescent : baseEnd_771612 < baseStart_771612 := by decide
  rcases family_descends (prefixWord ++ tailWord_771612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771642 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2]
def baseStart_771642 : Nat := 118140960795 + 771642 * 2 ^ 59
def prefixEnd_771642 : Nat := 4983230072969 + 3 ^ 40 * 771642 * 2
def baseEnd_771642 : Nat := 396223239196775180826289

theorem tailTrace_771642 : CollatzResearch.WordTrace tailWord_771642 prefixEnd_771642 396223239196775180826289 := by
  unfold tailWord_771642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036023967620073701673295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18762730580320196537795453 7036023967620073701673295)
  ·
    refine ⟨10554035951430110552509943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7036023967620073701673295 10554035951430110552509943)
    ·
      refine ⟨15831053927145165828764915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10554035951430110552509943 15831053927145165828764915)
      ·
        refine ⟨23746580890717748743147373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15831053927145165828764915 23746580890717748743147373)
        ·
          refine ⟨8904967834019155778680265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23746580890717748743147373 8904967834019155778680265)
          ·
            refine ⟨6678725875514366834010199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8904967834019155778680265 6678725875514366834010199)
            ·
              refine ⟨10018088813271550251015299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6678725875514366834010199 10018088813271550251015299)
              ·
                refine ⟨15027133219907325376522949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10018088813271550251015299 15027133219907325376522949)
                ·
                  refine ⟨2817587478732623508098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15027133219907325376522949 2817587478732623508098053)
                  ·
                    refine ⟨528297652262366907768385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817587478732623508098053 528297652262366907768385)
                    ·
                      refine ⟨396223239196775180826289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528297652262366907768385 396223239196775180826289)
                      ·
                        rfl

theorem cell23_771642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2].length) (baseStart_771642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771642 prefixEnd_771642 := by exact prefixLift 771642
  have htrace : WordTrace (prefixWord ++ tailWord_771642) baseStart_771642 baseEnd_771642 := by
    simpa [prefixWord, tailWord_771642, baseEnd_771642] using wordTrace_append hprefix tailTrace_771642
  have hstable : (prefixWord ++ tailWord_771642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771642).length < 2 ^ (prefixWord ++ tailWord_771642).sum := by decide
  have hdescent : baseEnd_771642 < baseStart_771642 := by decide
  rcases family_descends (prefixWord ++ tailWord_771642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771695 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 5, 5]
def baseStart_771695 : Nat := 118140960795 + 771695 * 2 ^ 59
def prefixEnd_771695 : Nat := 4983230072969 + 3 ^ 40 * 771695 * 2
def baseEnd_771695 : Nat := 132083484557154491154515

theorem tailTrace_771695 : CollatzResearch.WordTrace tailWord_771695 prefixEnd_771695 132083484557154491154515 := by
  unfold tailWord_771695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146028939288284858372539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18764019292858856572248359 28146028939288284858372539)
  ·
    refine ⟨42219043408932427287558809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28146028939288284858372539 42219043408932427287558809)
    ·
      refine ⟨31664282556699320465669107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42219043408932427287558809 31664282556699320465669107)
      ·
        refine ⟨47496423835048980698503661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31664282556699320465669107 47496423835048980698503661)
        ·
          refine ⟨17811158938143367761938873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47496423835048980698503661 17811158938143367761938873)
          ·
            refine ⟨13358369203607525821454155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17811158938143367761938873 13358369203607525821454155)
            ·
              refine ⟨20037553805411288732181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13358369203607525821454155 20037553805411288732181233)
              ·
                refine ⟨15028165354058466549135925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20037553805411288732181233 15028165354058466549135925)
                ·
                  refine ⟨1408890501942981238981493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15028165354058466549135925 1408890501942981238981493)
                  ·
                    refine ⟨132083484557154491154515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1408890501942981238981493 132083484557154491154515)
                    ·
                      rfl

theorem cell23_771695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_771695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771695 prefixEnd_771695 := by exact prefixLift 771695
  have htrace : WordTrace (prefixWord ++ tailWord_771695) baseStart_771695 baseEnd_771695 := by
    simpa [prefixWord, tailWord_771695, baseEnd_771695] using wordTrace_append hprefix tailTrace_771695
  have hstable : (prefixWord ++ tailWord_771695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771695).length < 2 ^ (prefixWord ++ tailWord_771695).sum := by decide
  have hdescent : baseEnd_771695 < baseStart_771695 := by decide
  rcases family_descends (prefixWord ++ tailWord_771695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771715 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4]
def baseStart_771715 : Nat := 118140960795 + 771715 * 2 ^ 59
def prefixEnd_771715 : Nat := 4983230072969 + 3 ^ 40 * 771715 * 2
def baseEnd_771715 : Nat := 396260723284553395213453

theorem tailTrace_771715 : CollatzResearch.WordTrace tailWord_771715 prefixEnd_771715 396260723284553395213453 := by
  unfold tailWord_771715
  simp only [CollatzResearch.WordTrace]
  refine ⟨28146758399215828274100599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18764505599477218849400399 28146758399215828274100599)
  ·
    refine ⟨42220137598823742411150899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28146758399215828274100599 42220137598823742411150899)
    ·
      refine ⟨63330206398235613616726349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42220137598823742411150899 63330206398235613616726349)
      ·
        refine ⟨23748827399338355106272381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63330206398235613616726349 23748827399338355106272381)
        ·
          refine ⟨8905810274751883164852143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23748827399338355106272381 8905810274751883164852143)
          ·
            refine ⟨13358715412127824747278215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8905810274751883164852143 13358715412127824747278215)
            ·
              refine ⟨20038073118191737120917323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13358715412127824747278215 20038073118191737120917323)
              ·
                refine ⟨30057109677287605681375985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20038073118191737120917323 30057109677287605681375985)
                ·
                  refine ⟨22542832257965704261031989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30057109677287605681375985 22542832257965704261031989)
                  ·
                    refine ⟨2113390524184284774471749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22542832257965704261031989 2113390524184284774471749)
                    ·
                      refine ⟨396260723284553395213453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2113390524184284774471749 396260723284553395213453)
                      ·
                        rfl

theorem cell23_771715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_771715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771715 prefixEnd_771715 := by exact prefixLift 771715
  have htrace : WordTrace (prefixWord ++ tailWord_771715) baseStart_771715 baseEnd_771715 := by
    simpa [prefixWord, tailWord_771715, baseEnd_771715] using wordTrace_append hprefix tailTrace_771715
  have hstable : (prefixWord ++ tailWord_771715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771715).length < 2 ^ (prefixWord ++ tailWord_771715).sum := by decide
  have hdescent : baseEnd_771715 < baseStart_771715 := by decide
  rcases family_descends (prefixWord ++ tailWord_771715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771716 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 6]
def baseStart_771716 : Nat := 118140960795 + 771716 * 2 ^ 59
def prefixEnd_771716 : Nat := 4983230072969 + 3 ^ 40 * 771716 * 2
def baseEnd_771716 : Nat := 44029026307245321255661

theorem tailTrace_771716 : CollatzResearch.WordTrace tailWord_771716 prefixEnd_771716 44029026307245321255661 := by
  unfold tailWord_771716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073397436106102722443501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18764529914808136963258001 14073397436106102722443501)
  ·
    refine ⟨5277524038539788520916313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14073397436106102722443501 5277524038539788520916313)
    ·
      refine ⟨3958143028904841390687235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5277524038539788520916313 3958143028904841390687235)
      ·
        refine ⟨5937214543357262086030853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958143028904841390687235 5937214543357262086030853)
        ·
          refine ⟨1113227726879486641130785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5937214543357262086030853 1113227726879486641130785)
          ·
            refine ⟨834920795159614980848089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1113227726879486641130785 834920795159614980848089)
            ·
              refine ⟨626190596369711235636067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834920795159614980848089 626190596369711235636067)
              ·
                refine ⟨939285894554566853454101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626190596369711235636067 939285894554566853454101)
                ·
                  refine ⟨44029026307245321255661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 939285894554566853454101 44029026307245321255661)
                  ·
                    rfl

theorem cell23_771716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_771716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771716 prefixEnd_771716 := by exact prefixLift 771716
  have htrace : WordTrace (prefixWord ++ tailWord_771716) baseStart_771716 baseEnd_771716 := by
    simpa [prefixWord, tailWord_771716, baseEnd_771716] using wordTrace_append hprefix tailTrace_771716
  have hstable : (prefixWord ++ tailWord_771716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771716).length < 2 ^ (prefixWord ++ tailWord_771716).sum := by decide
  have hdescent : baseEnd_771716 < baseStart_771716 := by decide
  rcases family_descends (prefixWord ++ tailWord_771716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771736 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2]
def baseStart_771736 : Nat := 118140960795 + 771736 * 2 ^ 59
def prefixEnd_771736 : Nat := 4983230072969 + 3 ^ 40 * 771736 * 2
def baseEnd_771736 : Nat := 396271506378297813050857

theorem tailTrace_771736 : CollatzResearch.WordTrace tailWord_771736 prefixEnd_771736 396271506378297813050857 := by
  unfold tailWord_771736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073762166069874430307531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18765016221426499240410041 14073762166069874430307531)
  ·
    refine ⟨21110643249104811645461297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14073762166069874430307531 21110643249104811645461297)
    ·
      refine ⟨15832982436828608734095973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21110643249104811645461297 15832982436828608734095973)
      ·
        refine ⟨2968684206905364137642995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15832982436828608734095973 2968684206905364137642995)
        ·
          refine ⟨4453026310358046206464493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968684206905364137642995 4453026310358046206464493)
          ·
            refine ⟨1669884866384267327424185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4453026310358046206464493 1669884866384267327424185)
            ·
              refine ⟨1252413649788200495568139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1669884866384267327424185 1252413649788200495568139)
              ·
                refine ⟨1878620474682300743352209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252413649788200495568139 1878620474682300743352209)
                ·
                  refine ⟨1408965356011725557514157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878620474682300743352209 1408965356011725557514157)
                  ·
                    refine ⟨528362008504397084067809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408965356011725557514157 528362008504397084067809)
                    ·
                      refine ⟨396271506378297813050857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528362008504397084067809 396271506378297813050857)
                      ·
                        rfl

theorem cell23_771736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_771736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771736 prefixEnd_771736 := by exact prefixLift 771736
  have htrace : WordTrace (prefixWord ++ tailWord_771736) baseStart_771736 baseEnd_771736 := by
    simpa [prefixWord, tailWord_771736, baseEnd_771736] using wordTrace_append hprefix tailTrace_771736
  have hstable : (prefixWord ++ tailWord_771736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771736).length < 2 ^ (prefixWord ++ tailWord_771736).sum := by decide
  have hdescent : baseEnd_771736 < baseStart_771736 := by decide
  rcases family_descends (prefixWord ++ tailWord_771736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771759 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 2, 4]
def baseStart_771759 : Nat := 118140960795 + 771759 * 2 ^ 59
def prefixEnd_771759 : Nat := 4983230072969 + 3 ^ 40 * 771759 * 2
def baseEnd_771759 : Nat := 132094438811117074354417

theorem tailTrace_771759 : CollatzResearch.WordTrace tailWord_771759 prefixEnd_771759 132094438811117074354417 := by
  unfold tailWord_771759
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148363211056423788702331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18765575474037615859134887 28148363211056423788702331)
  ·
    refine ⟨42222544816584635683053497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28148363211056423788702331 42222544816584635683053497)
    ·
      refine ⟨31666908612438476762290123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42222544816584635683053497 31666908612438476762290123)
      ·
        refine ⟨47500362918657715143435185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31666908612438476762290123 47500362918657715143435185)
        ·
          refine ⟨35625272188993286357576389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47500362918657715143435185 35625272188993286357576389)
          ·
            refine ⟨6679738535436241192045573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35625272188993286357576389 6679738535436241192045573)
            ·
              refine ⟨1252450975394295223508545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6679738535436241192045573 1252450975394295223508545)
              ·
                refine ⟨939338231545721417631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252450975394295223508545 939338231545721417631409)
                ·
                  refine ⟨704503673659291063223557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939338231545721417631409 704503673659291063223557)
                  ·
                    refine ⟨132094438811117074354417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704503673659291063223557 132094438811117074354417)
                    ·
                      rfl

theorem cell23_771759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_771759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771759 prefixEnd_771759 := by exact prefixLift 771759
  have htrace : WordTrace (prefixWord ++ tailWord_771759) baseStart_771759 baseEnd_771759 := by
    simpa [prefixWord, tailWord_771759, baseEnd_771759] using wordTrace_append hprefix tailTrace_771759
  have hstable : (prefixWord ++ tailWord_771759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771759).length < 2 ^ (prefixWord ++ tailWord_771759).sum := by decide
  have hdescent : baseEnd_771759 < baseStart_771759 := by decide
  rcases family_descends (prefixWord ++ tailWord_771759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771766 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_771766 : Nat := 118140960795 + 771766 * 2 ^ 59
def prefixEnd_771766 : Nat := 4983230072969 + 3 ^ 40 * 771766 * 2
def baseEnd_771766 : Nat := 396286910797932695675719

theorem tailTrace_771766 : CollatzResearch.WordTrace tailWord_771766 prefixEnd_771766 396286910797932695675719 := by
  unfold tailWord_771766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759288657626941499012947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18765745681354042656138101 1759288657626941499012947)
  ·
    refine ⟨2638932986440412248519421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759288657626941499012947 2638932986440412248519421)
    ·
      refine ⟨989599869915154593194783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2638932986440412248519421 989599869915154593194783)
      ·
        refine ⟨1484399804872731889792175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989599869915154593194783 1484399804872731889792175)
        ·
          refine ⟨2226599707309097834688263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484399804872731889792175 2226599707309097834688263)
          ·
            refine ⟨3339899560963646752032395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226599707309097834688263 3339899560963646752032395)
            ·
              refine ⟨5009849341445470128048593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339899560963646752032395 5009849341445470128048593)
              ·
                refine ⟨3757387006084102596036445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009849341445470128048593 3757387006084102596036445)
                ·
                  refine ⟨1409020127281538473513667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3757387006084102596036445 1409020127281538473513667)
                  ·
                    refine ⟨2113530190922307710270501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1409020127281538473513667 2113530190922307710270501)
                    ·
                      refine ⟨396286910797932695675719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2113530190922307710270501 396286910797932695675719)
                      ·
                        rfl

theorem cell23_771766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_771766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771766 prefixEnd_771766 := by exact prefixLift 771766
  have htrace : WordTrace (prefixWord ++ tailWord_771766) baseStart_771766 baseEnd_771766 := by
    simpa [prefixWord, tailWord_771766, baseEnd_771766] using wordTrace_append hprefix tailTrace_771766
  have hstable : (prefixWord ++ tailWord_771766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771766).length < 2 ^ (prefixWord ++ tailWord_771766).sum := by decide
  have hdescent : baseEnd_771766 < baseStart_771766 := by decide
  rcases family_descends (prefixWord ++ tailWord_771766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771772 : List Nat := [2, 2, 2, 3, 1, 2, 3, 8]
def baseStart_771772 : Nat := 118140960795 + 771772 * 2 ^ 59
def prefixEnd_771772 : Nat := 4983230072969 + 3 ^ 40 * 771772 * 2
def baseEnd_771772 : Nat := 14677407099328136007433

theorem tailTrace_771772 : CollatzResearch.WordTrace tailWord_771772 prefixEnd_771772 14677407099328136007433 := by
  unfold tailWord_771772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074418680004663504462785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18765891573339551339283713 14074418680004663504462785)
  ·
    refine ⟨10555814010003497628347089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14074418680004663504462785 10555814010003497628347089)
    ·
      refine ⟨7916860507502623221260317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10555814010003497628347089 7916860507502623221260317)
      ·
        refine ⟨2968822690313483707972619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7916860507502623221260317 2968822690313483707972619)
        ·
          refine ⟨4453234035470225561958929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968822690313483707972619 4453234035470225561958929)
          ·
            refine ⟨3339925526602669171469197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4453234035470225561958929 3339925526602669171469197)
            ·
              refine ⟨1252472072476000939300949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3339925526602669171469197 1252472072476000939300949)
              ·
                refine ⟨14677407099328136007433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1252472072476000939300949 14677407099328136007433)
                ·
                  rfl

theorem cell23_771772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 8].length) (baseStart_771772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771772 prefixEnd_771772 := by exact prefixLift 771772
  have htrace : WordTrace (prefixWord ++ tailWord_771772) baseStart_771772 baseEnd_771772 := by
    simpa [prefixWord, tailWord_771772, baseEnd_771772] using wordTrace_append hprefix tailTrace_771772
  have hstable : (prefixWord ++ tailWord_771772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771772).length < 2 ^ (prefixWord ++ tailWord_771772).sum := by decide
  have hdescent : baseEnd_771772 < baseStart_771772 := by decide
  rcases family_descends (prefixWord ++ tailWord_771772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771799 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_771799 : Nat := 118140960795 + 771799 * 2 ^ 59
def prefixEnd_771799 : Nat := 4983230072969 + 3 ^ 40 * 771799 * 2
def baseEnd_771799 : Nat := 396303855659531066563067

theorem tailTrace_771799 : CollatzResearch.WordTrace tailWord_771799 prefixEnd_771799 396303855659531066563067 := by
  unfold tailWord_771799
  simp only [CollatzResearch.WordTrace]
  refine ⟨28149822130911510620158451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18766548087274340413438967 28149822130911510620158451)
  ·
    refine ⟨42224733196367265930237677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28149822130911510620158451 42224733196367265930237677)
    ·
      refine ⟨15834274948637724723839129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42224733196367265930237677 15834274948637724723839129)
      ·
        refine ⟨11875706211478293542879347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15834274948637724723839129 11875706211478293542879347)
        ·
          refine ⟨17813559317217440314319021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11875706211478293542879347 17813559317217440314319021)
          ·
            refine ⟨6680084743956540117869633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17813559317217440314319021 6680084743956540117869633)
            ·
              refine ⟨5010063557967405088402225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6680084743956540117869633 5010063557967405088402225)
              ·
                refine ⟨3757547668475553816301669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010063557967405088402225 3757547668475553816301669)
                ·
                  refine ⟨704540187839166340556563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3757547668475553816301669 704540187839166340556563)
                  ·
                    refine ⟨1056810281758749510834845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704540187839166340556563 1056810281758749510834845)
                    ·
                      refine ⟨396303855659531066563067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056810281758749510834845 396303855659531066563067)
                      ·
                        rfl

theorem cell23_771799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_771799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771799 prefixEnd_771799 := by exact prefixLift 771799
  have htrace : WordTrace (prefixWord ++ tailWord_771799) baseStart_771799 baseEnd_771799 := by
    simpa [prefixWord, tailWord_771799, baseEnd_771799] using wordTrace_append hprefix tailTrace_771799
  have hstable : (prefixWord ++ tailWord_771799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771799).length < 2 ^ (prefixWord ++ tailWord_771799).sum := by decide
  have hdescent : baseEnd_771799 < baseStart_771799 := by decide
  rcases family_descends (prefixWord ++ tailWord_771799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771816 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_771816 : Nat := 118140960795 + 771816 * 2 ^ 59
def prefixEnd_771816 : Nat := 4983230072969 + 3 ^ 40 * 771816 * 2
def baseEnd_771816 : Nat := 396312584830657500050489

theorem tailTrace_771816 : CollatzResearch.WordTrace tailWord_771816 prefixEnd_771816 396312584830657500050489 := by
  unfold tailWord_771816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075221085924961261763651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18766961447899948349018201 14075221085924961261763651)
  ·
    refine ⟨21112831628887441892645477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075221085924961261763651 21112831628887441892645477)
    ·
      refine ⟨3958655930416395354871027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21112831628887441892645477 3958655930416395354871027)
      ·
        refine ⟨5937983895624593032306541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3958655930416395354871027 5937983895624593032306541)
        ·
          refine ⟨2226743960859222387114953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5937983895624593032306541 2226743960859222387114953)
          ·
            refine ⟨1670057970644416790336215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2226743960859222387114953 1670057970644416790336215)
            ·
              refine ⟨2505086955966625185504323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670057970644416790336215 2505086955966625185504323)
              ·
                refine ⟨3757630433949937778256485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505086955966625185504323 3757630433949937778256485)
                ·
                  refine ⟨704555706365613333423091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3757630433949937778256485 704555706365613333423091)
                  ·
                    refine ⟨1056833559548420000134637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 704555706365613333423091 1056833559548420000134637)
                    ·
                      refine ⟨396312584830657500050489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1056833559548420000134637 396312584830657500050489)
                      ·
                        rfl

theorem cell23_771816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_771816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771816 prefixEnd_771816 := by exact prefixLift 771816
  have htrace : WordTrace (prefixWord ++ tailWord_771816) baseStart_771816 baseEnd_771816 := by
    simpa [prefixWord, tailWord_771816, baseEnd_771816] using wordTrace_append hprefix tailTrace_771816
  have hstable : (prefixWord ++ tailWord_771816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771816).length < 2 ^ (prefixWord ++ tailWord_771816).sum := by decide
  have hdescent : baseEnd_771816 < baseStart_771816 := by decide
  rcases family_descends (prefixWord ++ tailWord_771816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771852 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_771852 : Nat := 118140960795 + 771852 * 2 ^ 59
def prefixEnd_771852 : Nat := 4983230072969 + 3 ^ 40 * 771852 * 2
def baseEnd_771852 : Nat := 396331070134219359200323

theorem tailTrace_771852 : CollatzResearch.WordTrace tailWord_771852 prefixEnd_771852 396331070134219359200323 := by
  unfold tailWord_771852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075877599859750335918905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18767836799813000447891873 14075877599859750335918905)
  ·
    refine ⟨10556908199894812751939179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14075877599859750335918905 10556908199894812751939179)
    ·
      refine ⟨15835362299842219127908769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10556908199894812751939179 15835362299842219127908769)
      ·
        refine ⟨11876521724881664345931577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15835362299842219127908769 11876521724881664345931577)
        ·
          refine ⟨8907391293661248259448683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876521724881664345931577 8907391293661248259448683)
          ·
            refine ⟨13361086940491872389173025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907391293661248259448683 13361086940491872389173025)
            ·
              refine ⟨10020815205368904291879769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13361086940491872389173025 10020815205368904291879769)
              ·
                refine ⟨7515611404026678218909827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020815205368904291879769 7515611404026678218909827)
                ·
                  refine ⟨11273417106040017328364741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515611404026678218909827 11273417106040017328364741)
                  ·
                    refine ⟨2113765707382503249068389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11273417106040017328364741 2113765707382503249068389)
                    ·
                      refine ⟨396331070134219359200323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2113765707382503249068389 396331070134219359200323)
                      ·
                        rfl

theorem cell23_771852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_771852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771852 prefixEnd_771852 := by exact prefixLift 771852
  have htrace : WordTrace (prefixWord ++ tailWord_771852) baseStart_771852 baseEnd_771852 := by
    simpa [prefixWord, tailWord_771852, baseEnd_771852] using wordTrace_append hprefix tailTrace_771852
  have hstable : (prefixWord ++ tailWord_771852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771852).length < 2 ^ (prefixWord ++ tailWord_771852).sum := by decide
  have hdescent : baseEnd_771852 < baseStart_771852 := by decide
  rcases family_descends (prefixWord ++ tailWord_771852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771872 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7]
def baseStart_771872 : Nat := 118140960795 + 771872 * 2 ^ 59
def prefixEnd_771872 : Nat := 4983230072969 + 3 ^ 40 * 771872 * 2
def baseEnd_771872 : Nat := 396341339747309280950231

theorem tailTrace_771872 : CollatzResearch.WordTrace tailWord_771872 prefixEnd_771872 396341339747309280950231 := by
  unfold tailWord_771872
  simp only [CollatzResearch.WordTrace]
  refine ⟨14076242329823522043782935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18768323106431362725043913 14076242329823522043782935)
  ·
    refine ⟨21114363494735283065674403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14076242329823522043782935 21114363494735283065674403)
    ·
      refine ⟨31671545242102924598511605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21114363494735283065674403 31671545242102924598511605)
      ·
        refine ⟨2969207366447149181110463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31671545242102924598511605 2969207366447149181110463)
        ·
          refine ⟨4453811049670723771665695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969207366447149181110463 4453811049670723771665695)
          ·
            refine ⟨6680716574506085657498543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453811049670723771665695 6680716574506085657498543)
            ·
              refine ⟨10021074861759128486247815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680716574506085657498543 10021074861759128486247815)
              ·
                refine ⟨15031612292638692729371723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021074861759128486247815 15031612292638692729371723)
                ·
                  refine ⟨22547418438958039094057585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15031612292638692729371723 22547418438958039094057585)
                  ·
                    refine ⟨16910563829218529320543189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22547418438958039094057585 16910563829218529320543189)
                    ·
                      refine ⟨396341339747309280950231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16910563829218529320543189 396341339747309280950231)
                      ·
                        rfl

theorem cell23_771872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_771872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771872 prefixEnd_771872 := by exact prefixLift 771872
  have htrace : WordTrace (prefixWord ++ tailWord_771872) baseStart_771872 baseEnd_771872 := by
    simpa [prefixWord, tailWord_771872, baseEnd_771872] using wordTrace_append hprefix tailTrace_771872
  have hstable : (prefixWord ++ tailWord_771872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771872).length < 2 ^ (prefixWord ++ tailWord_771872).sum := by decide
  have hdescent : baseEnd_771872 < baseStart_771872 := by decide
  rcases family_descends (prefixWord ++ tailWord_771872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771890 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2]
def baseStart_771890 : Nat := 118140960795 + 771890 * 2 ^ 59
def prefixEnd_771890 : Nat := 4983230072969 + 3 ^ 40 * 771890 * 2
def baseEnd_771890 : Nat := 396350582399090210525149

theorem tailTrace_771890 : CollatzResearch.WordTrace tailWord_771890 prefixEnd_771890 396350582399090210525149 := by
  unfold tailWord_771890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7038285293395458290430281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18768760782387888774480749 7038285293395458290430281)
  ·
    refine ⟨5278713970046593717822711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7038285293395458290430281 5278713970046593717822711)
    ·
      refine ⟨7918070955069890576734067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278713970046593717822711 7918070955069890576734067)
      ·
        refine ⟨11877106432604835865101101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7918070955069890576734067 11877106432604835865101101)
        ·
          refine ⟨4453914912226813449412913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11877106432604835865101101 4453914912226813449412913)
          ·
            refine ⟨3340436184170110087059685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4453914912226813449412913 3340436184170110087059685)
            ·
              refine ⟨626331784531895641323691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3340436184170110087059685 626331784531895641323691)
              ·
                refine ⟨939497676797843461985537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626331784531895641323691 939497676797843461985537)
                ·
                  refine ⟨704623257598382596489153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939497676797843461985537 704623257598382596489153)
                  ·
                    refine ⟨528467443198786947366865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 704623257598382596489153 528467443198786947366865)
                    ·
                      refine ⟨396350582399090210525149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528467443198786947366865 396350582399090210525149)
                      ·
                        rfl

theorem cell23_771890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_771890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771890 prefixEnd_771890 := by exact prefixLift 771890
  have htrace : WordTrace (prefixWord ++ tailWord_771890) baseStart_771890 baseEnd_771890 := by
    simpa [prefixWord, tailWord_771890, baseEnd_771890] using wordTrace_append hprefix tailTrace_771890
  have hstable : (prefixWord ++ tailWord_771890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771890).length < 2 ^ (prefixWord ++ tailWord_771890).sum := by decide
  have hdescent : baseEnd_771890 < baseStart_771890 := by decide
  rcases family_descends (prefixWord ++ tailWord_771890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771909 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_771909 : Nat := 118140960795 + 771909 * 2 ^ 59
def prefixEnd_771909 : Nat := 4983230072969 + 3 ^ 40 * 771909 * 2
def baseEnd_771909 : Nat := 132120112843841878729187

theorem tailTrace_771909 : CollatzResearch.WordTrace tailWord_771909 prefixEnd_771909 132120112843841878729187 := by
  unfold tailWord_771909
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153834160512999406662781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18769222773675332937775187 28153834160512999406662781)
  ·
    refine ⟨10557687810192374777498543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28153834160512999406662781 10557687810192374777498543)
    ·
      refine ⟨15836531715288562166247815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10557687810192374777498543 15836531715288562166247815)
      ·
        refine ⟨23754797572932843249371723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15836531715288562166247815 23754797572932843249371723)
        ·
          refine ⟨35632196359399264874057585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23754797572932843249371723 35632196359399264874057585)
          ·
            refine ⟨26724147269549448655543189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35632196359399264874057585 26724147269549448655543189)
            ·
              refine ⟨1252694403260130405728587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26724147269549448655543189 1252694403260130405728587)
              ·
                refine ⟨1879041604890195608592881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1252694403260130405728587 1879041604890195608592881)
                ·
                  refine ⟨1409281203667646706444661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1879041604890195608592881 1409281203667646706444661)
                  ·
                    refine ⟨132120112843841878729187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1409281203667646706444661 132120112843841878729187)
                    ·
                      rfl

theorem cell23_771909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_771909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771909 prefixEnd_771909 := by exact prefixLift 771909
  have htrace : WordTrace (prefixWord ++ tailWord_771909) baseStart_771909 baseEnd_771909 := by
    simpa [prefixWord, tailWord_771909, baseEnd_771909] using wordTrace_append hprefix tailTrace_771909
  have hstable : (prefixWord ++ tailWord_771909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771909).length < 2 ^ (prefixWord ++ tailWord_771909).sum := by decide
  have hdescent : baseEnd_771909 < baseStart_771909 := by decide
  rcases family_descends (prefixWord ++ tailWord_771909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771929 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 4]
def baseStart_771929 : Nat := 118140960795 + 771929 * 2 ^ 59
def prefixEnd_771929 : Nat := 4983230072969 + 3 ^ 40 * 771929 * 2
def baseEnd_771929 : Nat := 396370608144615557937469

theorem tailTrace_771929 : CollatzResearch.WordTrace tailWord_771929 prefixEnd_771929 396370608144615557937469 := by
  unfold tailWord_771929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28154563620440542822390841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18769709080293695214927227 28154563620440542822390841)
  ·
    refine ⟨21115922715330407116793131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28154563620440542822390841 21115922715330407116793131)
    ·
      refine ⟨31673884072995610675189697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21115922715330407116793131 31673884072995610675189697)
      ·
        refine ⟨23755413054746708006392273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31673884072995610675189697 23755413054746708006392273)
        ·
          refine ⟨17816559791060031004794205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23755413054746708006392273 17816559791060031004794205)
          ·
            refine ⟨6681209921647511626797827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17816559791060031004794205 6681209921647511626797827)
            ·
              refine ⟨10021814882471267440196741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6681209921647511626797827 10021814882471267440196741)
              ·
                refine ⟨1879090290463362645036889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10021814882471267440196741 1879090290463362645036889)
                ·
                  refine ⟨1409317717847521983777667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1879090290463362645036889 1409317717847521983777667)
                  ·
                    refine ⟨2113976576771282975666501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1409317717847521983777667 2113976576771282975666501)
                    ·
                      refine ⟨396370608144615557937469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2113976576771282975666501 396370608144615557937469)
                      ·
                        rfl

theorem cell23_771929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_771929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771929 prefixEnd_771929 := by exact prefixLift 771929
  have htrace : WordTrace (prefixWord ++ tailWord_771929) baseStart_771929 baseEnd_771929 := by
    simpa [prefixWord, tailWord_771929, baseEnd_771929] using wordTrace_append hprefix tailTrace_771929
  have hstable : (prefixWord ++ tailWord_771929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771929).length < 2 ^ (prefixWord ++ tailWord_771929).sum := by decide
  have hdescent : baseEnd_771929 < baseStart_771929 := by decide
  rcases family_descends (prefixWord ++ tailWord_771929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771952 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 10]
def baseStart_771952 : Nat := 118140960795 + 771952 * 2 ^ 59
def prefixEnd_771952 : Nat := 4983230072969 + 3 ^ 40 * 771952 * 2
def baseEnd_771952 : Nat := 44042490911074329772207

theorem tailTrace_771952 : CollatzResearch.WordTrace tailWord_771952 prefixEnd_771952 44042490911074329772207 := by
  unfold tailWord_771952
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077701249678608875239055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18770268332904811833652073 14077701249678608875239055)
  ·
    refine ⟨21116551874517913312858583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14077701249678608875239055 21116551874517913312858583)
    ·
      refine ⟨31674827811776869969287875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21116551874517913312858583 31674827811776869969287875)
      ·
        refine ⟨47512241717665304953931813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31674827811776869969287875 47512241717665304953931813)
        ·
          refine ⟨8908545322062244678862215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47512241717665304953931813 8908545322062244678862215)
          ·
            refine ⟨13362817983093367018293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908545322062244678862215 13362817983093367018293323)
            ·
              refine ⟨20044226974640050527439985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362817983093367018293323 20044226974640050527439985)
              ·
                refine ⟨15033170230980037895579989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20044226974640050527439985 15033170230980037895579989)
                ·
                  refine ⟨44042490911074329772207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15033170230980037895579989 44042490911074329772207)
                  ·
                    rfl

theorem cell23_771952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 10].length) (baseStart_771952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771952 prefixEnd_771952 := by exact prefixLift 771952
  have htrace : WordTrace (prefixWord ++ tailWord_771952) baseStart_771952 baseEnd_771952 := by
    simpa [prefixWord, tailWord_771952, baseEnd_771952] using wordTrace_append hprefix tailTrace_771952
  have hstable : (prefixWord ++ tailWord_771952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771952).length < 2 ^ (prefixWord ++ tailWord_771952).sum := by decide
  have hdescent : baseEnd_771952 < baseStart_771952 := by decide
  rcases family_descends (prefixWord ++ tailWord_771952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771973 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_771973 : Nat := 118140960795 + 771973 * 2 ^ 59
def prefixEnd_771973 : Nat := 4983230072969 + 3 ^ 40 * 771973 * 2
def baseEnd_771973 : Nat := 132131067097804461929089

theorem tailTrace_771973 : CollatzResearch.WordTrace tailWord_771973 prefixEnd_771973 132131067097804461929089 := by
  unfold tailWord_771973
  simp only [CollatzResearch.WordTrace]
  refine ⟨28156168432281138336992573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18770778954854092224661715 28156168432281138336992573)
  ·
    refine ⟨10558563162105426876372215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28156168432281138336992573 10558563162105426876372215)
    ·
      refine ⟨15837844743158140314558323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10558563162105426876372215 15837844743158140314558323)
      ·
        refine ⟨23756767114737210471837485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15837844743158140314558323 23756767114737210471837485)
        ·
          refine ⟨8908787668026453926939057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23756767114737210471837485 8908787668026453926939057)
          ·
            refine ⟨6681590751019840445204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8908787668026453926939057 6681590751019840445204293)
            ·
              refine ⟨1252798265816220083475805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6681590751019840445204293 1252798265816220083475805)
              ·
                refine ⟨469799349681082531303427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252798265816220083475805 469799349681082531303427)
                ·
                  refine ⟨704699024521623796955141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469799349681082531303427 704699024521623796955141)
                  ·
                    refine ⟨132131067097804461929089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704699024521623796955141 132131067097804461929089)
                    ·
                      rfl

theorem cell23_771973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_771973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771973 prefixEnd_771973 := by exact prefixLift 771973
  have htrace : WordTrace (prefixWord ++ tailWord_771973) baseStart_771973 baseEnd_771973 := by
    simpa [prefixWord, tailWord_771973, baseEnd_771973] using wordTrace_append hprefix tailTrace_771973
  have hstable : (prefixWord ++ tailWord_771973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771973).length < 2 ^ (prefixWord ++ tailWord_771973).sum := by decide
  have hdescent : baseEnd_771973 < baseStart_771973 := by decide
  rcases family_descends (prefixWord ++ tailWord_771973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_771986 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_771986 : Nat := 118140960795 + 771986 * 2 ^ 59
def prefixEnd_771986 : Nat := 4983230072969 + 3 ^ 40 * 771986 * 2
def baseEnd_771986 : Nat := 44044430726880203880523

theorem tailTrace_771986 : CollatzResearch.WordTrace tailWord_771986 prefixEnd_771986 44044430726880203880523 := by
  unfold tailWord_771986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7039160645308510389303953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18771095054156027704810541 7039160645308510389303953)
  ·
    refine ⟨5279370483981382791977965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7039160645308510389303953 5279370483981382791977965)
    ·
      refine ⟨1979763931493018546991737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5279370483981382791977965 1979763931493018546991737)
      ·
        refine ⟨1484822948619763910243803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1979763931493018546991737 1484822948619763910243803)
        ·
          refine ⟨2227234422929645865365705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484822948619763910243803 2227234422929645865365705)
          ·
            refine ⟨1670425817197234399024279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2227234422929645865365705 1670425817197234399024279)
            ·
              refine ⟨2505638725795851598536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670425817197234399024279 2505638725795851598536419)
              ·
                refine ⟨3758458088693777397804629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505638725795851598536419 3758458088693777397804629)
                ·
                  refine ⟨44044430726880203880523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3758458088693777397804629 44044430726880203880523)
                  ·
                    rfl

theorem cell23_771986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_771986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_771986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_771986 prefixEnd_771986 := by exact prefixLift 771986
  have htrace : WordTrace (prefixWord ++ tailWord_771986) baseStart_771986 baseEnd_771986 := by
    simpa [prefixWord, tailWord_771986, baseEnd_771986] using wordTrace_append hprefix tailTrace_771986
  have hstable : (prefixWord ++ tailWord_771986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_771986).length < 2 ^ (prefixWord ++ tailWord_771986).sum := by decide
  have hdescent : baseEnd_771986 < baseStart_771986 := by decide
  rcases family_descends (prefixWord ++ tailWord_771986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772046 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_772046 : Nat := 118140960795 + 772046 * 2 ^ 59
def prefixEnd_772046 : Nat := 4983230072969 + 3 ^ 40 * 772046 * 2
def baseEnd_772046 : Nat := 132143561793730533391477

theorem tailTrace_772046 : CollatzResearch.WordTrace tailWord_772046 prefixEnd_772046 132143561793730533391477 := by
  unfold tailWord_772046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519853870127083975549999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18772553974011114536266661 3519853870127083975549999)
  ·
    refine ⟨5279780805190625963324999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519853870127083975549999 5279780805190625963324999)
    ·
      refine ⟨7919671207785938944987499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279780805190625963324999 7919671207785938944987499)
      ·
        refine ⟨11879506811678908417481249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919671207785938944987499 11879506811678908417481249)
        ·
          refine ⟨8909630108759181313110937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879506811678908417481249 8909630108759181313110937)
          ·
            refine ⟨6682222581569385984833203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909630108759181313110937 6682222581569385984833203)
            ·
              refine ⟨10023333872354078977249805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682222581569385984833203 10023333872354078977249805)
              ·
                refine ⟨3758750202132779616468677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10023333872354078977249805 3758750202132779616468677)
                ·
                  refine ⟨704765662899896178087877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3758750202132779616468677 704765662899896178087877)
                  ·
                    refine ⟨132143561793730533391477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704765662899896178087877 132143561793730533391477)
                    ·
                      rfl

theorem cell23_772046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_772046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772046 prefixEnd_772046 := by exact prefixLift 772046
  have htrace : WordTrace (prefixWord ++ tailWord_772046) baseStart_772046 baseEnd_772046 := by
    simpa [prefixWord, tailWord_772046, baseEnd_772046] using wordTrace_append hprefix tailTrace_772046
  have hstable : (prefixWord ++ tailWord_772046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772046).length < 2 ^ (prefixWord ++ tailWord_772046).sum := by decide
  have hdescent : baseEnd_772046 < baseStart_772046 := by decide
  rcases family_descends (prefixWord ++ tailWord_772046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772049 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_772049 : Nat := 118140960795 + 772049 * 2 ^ 59
def prefixEnd_772049 : Nat := 4983230072969 + 3 ^ 40 * 772049 * 2
def baseEnd_772049 : Nat := 396432225823155088436917

theorem tailTrace_772049 : CollatzResearch.WordTrace tailWord_772049 prefixEnd_772049 396432225823155088436917 := by
  unfold tailWord_772049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158940380005803316759201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18772626920003868877839467 28158940380005803316759201)
  ·
    refine ⟨21119205285004352487569401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28158940380005803316759201 21119205285004352487569401)
    ·
      refine ⟨15839403963753264365677051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21119205285004352487569401 15839403963753264365677051)
      ·
        refine ⟨23759105945629896548515577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15839403963753264365677051 23759105945629896548515577)
        ·
          refine ⟨17819329459222422411386683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23759105945629896548515577 17819329459222422411386683)
          ·
            refine ⟨26728994188833633617080025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17819329459222422411386683 26728994188833633617080025)
            ·
              refine ⟨20046745641625225212810019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26728994188833633617080025 20046745641625225212810019)
              ·
                refine ⟨30070118462437837819215029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20046745641625225212810019 30070118462437837819215029)
                ·
                  refine ⟨2819073605853547295551409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30070118462437837819215029 2819073605853547295551409)
                  ·
                    refine ⟨2114305204390160471663557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819073605853547295551409 2114305204390160471663557)
                    ·
                      refine ⟨396432225823155088436917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2114305204390160471663557 396432225823155088436917)
                      ·
                        rfl

theorem cell23_772049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_772049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772049 prefixEnd_772049 := by exact prefixLift 772049
  have htrace : WordTrace (prefixWord ++ tailWord_772049) baseStart_772049 baseEnd_772049 := by
    simpa [prefixWord, tailWord_772049, baseEnd_772049] using wordTrace_append hprefix tailTrace_772049
  have hstable : (prefixWord ++ tailWord_772049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772049).length < 2 ^ (prefixWord ++ tailWord_772049).sum := by decide
  have hdescent : baseEnd_772049 < baseStart_772049 := by decide
  rcases family_descends (prefixWord ++ tailWord_772049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772056 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3]
def baseStart_772056 : Nat := 118140960795 + 772056 * 2 ^ 59
def prefixEnd_772056 : Nat := 4983230072969 + 3 ^ 40 * 772056 * 2
def baseEnd_772056 : Nat := 396435820187736561049385

theorem tailTrace_772056 : CollatzResearch.WordTrace tailWord_772056 prefixEnd_772056 396435820187736561049385 := by
  unfold tailWord_772056
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079597845490221756132011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18772797127320295674842681 14079597845490221756132011)
  ·
    refine ⟨21119396768235332634198017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14079597845490221756132011 21119396768235332634198017)
    ·
      refine ⟨15839547576176499475648513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21119396768235332634198017 15839547576176499475648513)
      ·
        refine ⟨11879660682132374606736385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15839547576176499475648513 11879660682132374606736385)
        ·
          refine ⟨8909745511599280955052289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879660682132374606736385 8909745511599280955052289)
          ·
            refine ⟨6682309133699460716289217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8909745511599280955052289 6682309133699460716289217)
            ·
              refine ⟨5011731850274595537216913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682309133699460716289217 5011731850274595537216913)
              ·
                refine ⟨3758798887705946652912685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011731850274595537216913 3758798887705946652912685)
                ·
                  refine ⟨1409549582889729994842257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3758798887705946652912685 1409549582889729994842257)
                  ·
                    refine ⟨1057162187167297496131693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1409549582889729994842257 1057162187167297496131693)
                    ·
                      refine ⟨396435820187736561049385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1057162187167297496131693 396435820187736561049385)
                      ·
                        rfl

theorem cell23_772056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_772056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772056 prefixEnd_772056 := by exact prefixLift 772056
  have htrace : WordTrace (prefixWord ++ tailWord_772056) baseStart_772056 baseEnd_772056 := by
    simpa [prefixWord, tailWord_772056, baseEnd_772056] using wordTrace_append hprefix tailTrace_772056
  have hstable : (prefixWord ++ tailWord_772056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772056).length < 2 ^ (prefixWord ++ tailWord_772056).sum := by decide
  have hdescent : baseEnd_772056 < baseStart_772056 := by decide
  rcases family_descends (prefixWord ++ tailWord_772056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772063 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 2, 4]
def baseStart_772063 : Nat := 118140960795 + 772063 * 2 ^ 59
def prefixEnd_772063 : Nat := 4983230072969 + 3 ^ 40 * 772063 * 2
def baseEnd_772063 : Nat := 132146471517439344553951

theorem tailTrace_772063 : CollatzResearch.WordTrace tailWord_772063 prefixEnd_772063 132146471517439344553951 := by
  unfold tailWord_772063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159451001955083707768843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18772967334636722471845895 28159451001955083707768843)
  ·
    refine ⟨42239176502932625561653265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28159451001955083707768843 42239176502932625561653265)
    ·
      refine ⟨31679382377199469171239949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42239176502932625561653265 31679382377199469171239949)
      ·
        refine ⟨11879768391449800939214981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31679382377199469171239949 11879768391449800939214981)
        ·
          refine ⟨2227456573396837676102809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11879768391449800939214981 2227456573396837676102809)
          ·
            refine ⟨1670592430047628257077107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2227456573396837676102809 1670592430047628257077107)
            ·
              refine ⟨2505888645071442385615661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670592430047628257077107 2505888645071442385615661)
              ·
                refine ⟨939708241901790894605873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505888645071442385615661 939708241901790894605873)
                ·
                  refine ⟨704781181426343170954405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 939708241901790894605873 704781181426343170954405)
                  ·
                    refine ⟨132146471517439344553951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 704781181426343170954405 132146471517439344553951)
                    ·
                      rfl

theorem cell23_772063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_772063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772063 prefixEnd_772063 := by exact prefixLift 772063
  have htrace : WordTrace (prefixWord ++ tailWord_772063) baseStart_772063 baseEnd_772063 := by
    simpa [prefixWord, tailWord_772063, baseEnd_772063] using wordTrace_append hprefix tailTrace_772063
  have hstable : (prefixWord ++ tailWord_772063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772063).length < 2 ^ (prefixWord ++ tailWord_772063).sum := by decide
  have hdescent : baseEnd_772063 < baseStart_772063 := by decide
  rcases family_descends (prefixWord ++ tailWord_772063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772099 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_772099 : Nat := 118140960795 + 772099 * 2 ^ 59
def prefixEnd_772099 : Nat := 4983230072969 + 3 ^ 40 * 772099 * 2
def baseEnd_772099 : Nat := 396457899855879892811687

theorem tailTrace_772099 : CollatzResearch.WordTrace tailWord_772099 prefixEnd_772099 396457899855879892811687 := by
  unfold tailWord_772099
  simp only [CollatzResearch.WordTrace]
  refine ⟨28160764029824661856079351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18773842686549774570719567 28160764029824661856079351)
  ·
    refine ⟨42241146044736992784119027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28160764029824661856079351 42241146044736992784119027)
    ·
      refine ⟨63361719067105489176178541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42241146044736992784119027 63361719067105489176178541)
      ·
        refine ⟨23760644650164558441066953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63361719067105489176178541 23760644650164558441066953)
        ·
          refine ⟨17820483487623418830800215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23760644650164558441066953 17820483487623418830800215)
          ·
            refine ⟨26730725231435128246200323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17820483487623418830800215 26730725231435128246200323)
            ·
              refine ⟨40096087847152692369300485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26730725231435128246200323 40096087847152692369300485)
              ·
                refine ⟨7518016471341129819243841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40096087847152692369300485 7518016471341129819243841)
                ·
                  refine ⟨5638512353505847364432881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7518016471341129819243841 5638512353505847364432881)
                  ·
                    refine ⟨4228884265129385523324661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5638512353505847364432881 4228884265129385523324661)
                    ·
                      refine ⟨396457899855879892811687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4228884265129385523324661 396457899855879892811687)
                      ·
                        rfl

theorem cell23_772099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_772099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772099 prefixEnd_772099 := by exact prefixLift 772099
  have htrace : WordTrace (prefixWord ++ tailWord_772099) baseStart_772099 baseEnd_772099 := by
    simpa [prefixWord, tailWord_772099, baseEnd_772099] using wordTrace_append hprefix tailTrace_772099
  have hstable : (prefixWord ++ tailWord_772099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772099).length < 2 ^ (prefixWord ++ tailWord_772099).sum := by decide
  have hdescent : baseEnd_772099 < baseStart_772099 := by decide
  rcases family_descends (prefixWord ++ tailWord_772099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772130 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_772130 : Nat := 118140960795 + 772130 * 2 ^ 59
def prefixEnd_772130 : Nat := 4983230072969 + 3 ^ 40 * 772130 * 2
def baseEnd_772130 : Nat := 396473817756169271524045

theorem tailTrace_772130 : CollatzResearch.WordTrace tailWord_772130 prefixEnd_772130 396473817756169271524045 := by
  unfold tailWord_772130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040473673178088537614461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18774596461808236100305229 7040473673178088537614461)
  ·
    refine ⟨2640177627441783201605423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7040473673178088537614461 2640177627441783201605423)
    ·
      refine ⟨3960266441162674802408135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640177627441783201605423 3960266441162674802408135)
      ·
        refine ⟨5940399661744012203612203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960266441162674802408135 5940399661744012203612203)
        ·
          refine ⟨8910599492616018305418305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940399661744012203612203 8910599492616018305418305)
          ·
            refine ⟨6682949619462013729063729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910599492616018305418305 6682949619462013729063729)
            ·
              refine ⟨5012212214596510296797797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6682949619462013729063729 5012212214596510296797797)
              ·
                refine ⟨939789790236845680649587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5012212214596510296797797 939789790236845680649587)
                ·
                  refine ⟨1409684685355268520974381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939789790236845680649587 1409684685355268520974381)
                  ·
                    refine ⟨528631757008225695365393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409684685355268520974381 528631757008225695365393)
                    ·
                      refine ⟨396473817756169271524045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528631757008225695365393 396473817756169271524045)
                      ·
                        rfl

theorem cell23_772130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_772130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772130 prefixEnd_772130 := by exact prefixLift 772130
  have htrace : WordTrace (prefixWord ++ tailWord_772130) baseStart_772130 baseEnd_772130 := by
    simpa [prefixWord, tailWord_772130, baseEnd_772130] using wordTrace_append hprefix tailTrace_772130
  have hstable : (prefixWord ++ tailWord_772130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772130).length < 2 ^ (prefixWord ++ tailWord_772130).sum := by decide
  have hdescent : baseEnd_772130 < baseStart_772130 := by decide
  rcases family_descends (prefixWord ++ tailWord_772130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772156 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_772156 : Nat := 118140960795 + 772156 * 2 ^ 59
def prefixEnd_772156 : Nat := 4983230072969 + 3 ^ 40 * 772156 * 2
def baseEnd_772156 : Nat := 396487168253186169798925

theorem tailTrace_772156 : CollatzResearch.WordTrace tailWord_772156 prefixEnd_772156 396487168253186169798925 := by
  unfold tailWord_772156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14081421495309080295452161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18775228660412107060602881 14081421495309080295452161)
  ·
    refine ⟨10561066121481810221589121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14081421495309080295452161 10561066121481810221589121)
    ·
      refine ⟨7920799591111357666191841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10561066121481810221589121 7920799591111357666191841)
      ·
        refine ⟨5940599693333518249643881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7920799591111357666191841 5940599693333518249643881)
        ·
          refine ⟨4455449770000138687232911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940599693333518249643881 4455449770000138687232911)
          ·
            refine ⟨6683174655000208030849367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455449770000138687232911 6683174655000208030849367)
            ·
              refine ⟨10024761982500312046274051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683174655000208030849367 10024761982500312046274051)
              ·
                refine ⟨15037142973750468069411077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10024761982500312046274051 15037142973750468069411077)
                ·
                  refine ⟨2819464307578212763014577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15037142973750468069411077 2819464307578212763014577)
                  ·
                    refine ⟨2114598230683659572260933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819464307578212763014577 2114598230683659572260933)
                    ·
                      refine ⟨396487168253186169798925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2114598230683659572260933 396487168253186169798925)
                      ·
                        rfl

theorem cell23_772156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_772156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772156 prefixEnd_772156 := by exact prefixLift 772156
  have htrace : WordTrace (prefixWord ++ tailWord_772156) baseStart_772156 baseEnd_772156 := by
    simpa [prefixWord, tailWord_772156, baseEnd_772156] using wordTrace_append hprefix tailTrace_772156
  have hstable : (prefixWord ++ tailWord_772156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772156).length < 2 ^ (prefixWord ++ tailWord_772156).sum := by decide
  have hdescent : baseEnd_772156 < baseStart_772156 := by decide
  rcases family_descends (prefixWord ++ tailWord_772156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772160 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2]
def baseStart_772160 : Nat := 118140960795 + 772160 * 2 ^ 59
def prefixEnd_772160 : Nat := 4983230072969 + 3 ^ 40 * 772160 * 2
def baseEnd_772160 : Nat := 396489222175804154148907

theorem tailTrace_772160 : CollatzResearch.WordTrace tailWord_772160 prefixEnd_772160 396489222175804154148907 := by
  unfold tailWord_772160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14081494441301834637024967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18775325921735779516033289 14081494441301834637024967)
  ·
    refine ⟨21122241661952751955537451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14081494441301834637024967 21122241661952751955537451)
    ·
      refine ⟨31683362492929127933306177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21122241661952751955537451 31683362492929127933306177)
      ·
        refine ⟨23762521869696845949979633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31683362492929127933306177 23762521869696845949979633)
        ·
          refine ⟨17821891402272634462484725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23762521869696845949979633 17821891402272634462484725)
          ·
            refine ⟨1670802318963059480857943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17821891402272634462484725 1670802318963059480857943)
            ·
              refine ⟨2506203478444589221286915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670802318963059480857943 2506203478444589221286915)
              ·
                refine ⟨3759305217666883831930373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506203478444589221286915 3759305217666883831930373)
                ·
                  refine ⟨704869728312540718486945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3759305217666883831930373 704869728312540718486945)
                  ·
                    refine ⟨528652296234405538865209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 704869728312540718486945 528652296234405538865209)
                    ·
                      refine ⟨396489222175804154148907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528652296234405538865209 396489222175804154148907)
                      ·
                        rfl

theorem cell23_772160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2].length) (baseStart_772160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772160 prefixEnd_772160 := by exact prefixLift 772160
  have htrace : WordTrace (prefixWord ++ tailWord_772160) baseStart_772160 baseEnd_772160 := by
    simpa [prefixWord, tailWord_772160, baseEnd_772160] using wordTrace_append hprefix tailTrace_772160
  have hstable : (prefixWord ++ tailWord_772160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772160).length < 2 ^ (prefixWord ++ tailWord_772160).sum := by decide
  have hdescent : baseEnd_772160 < baseStart_772160 := by decide
  rcases family_descends (prefixWord ++ tailWord_772160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772173 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_772173 : Nat := 118140960795 + 772173 * 2 ^ 59
def prefixEnd_772173 : Nat := 4983230072969 + 3 ^ 40 * 772173 * 2
def baseEnd_772173 : Nat := 396495897424312603286347

theorem tailTrace_772173 : CollatzResearch.WordTrace tailWord_772173 prefixEnd_772173 396495897424312603286347 := by
  unfold tailWord_772173
  simp only [CollatzResearch.WordTrace]
  refine ⟨28163463031556572494273173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18775642021037714996182115 28163463031556572494273173)
  ·
    refine ⟨1320162329604214335669055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28163463031556572494273173 1320162329604214335669055)
    ·
      refine ⟨1980243494406321503503583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320162329604214335669055 1980243494406321503503583)
      ·
        refine ⟨2970365241609482255255375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980243494406321503503583 2970365241609482255255375)
        ·
          refine ⟨4455547862414223382883063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970365241609482255255375 4455547862414223382883063)
          ·
            refine ⟨6683321793621335074324595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455547862414223382883063 6683321793621335074324595)
            ·
              refine ⟨10024982690432002611486893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683321793621335074324595 10024982690432002611486893)
              ·
                refine ⟨3759368508912000979307585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10024982690432002611486893 3759368508912000979307585)
                ·
                  refine ⟨2819526381684000734480689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3759368508912000979307585 2819526381684000734480689)
                  ·
                    refine ⟨2114644786263000550860517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2819526381684000734480689 2114644786263000550860517)
                    ·
                      refine ⟨396495897424312603286347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2114644786263000550860517 396495897424312603286347)
                      ·
                        rfl

theorem cell23_772173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_772173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772173 prefixEnd_772173 := by exact prefixLift 772173
  have htrace : WordTrace (prefixWord ++ tailWord_772173) baseStart_772173 baseEnd_772173 := by
    simpa [prefixWord, tailWord_772173, baseEnd_772173] using wordTrace_append hprefix tailTrace_772173
  have hstable : (prefixWord ++ tailWord_772173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772173).length < 2 ^ (prefixWord ++ tailWord_772173).sum := by decide
  have hdescent : baseEnd_772173 < baseStart_772173 := by decide
  rcases family_descends (prefixWord ++ tailWord_772173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772196 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_772196 : Nat := 118140960795 + 772196 * 2 ^ 59
def prefixEnd_772196 : Nat := 4983230072969 + 3 ^ 40 * 772196 * 2
def baseEnd_772196 : Nat := 132169235826455337766247

theorem tailTrace_772196 : CollatzResearch.WordTrace tailWord_772196 prefixEnd_772196 132169235826455337766247 := by
  unfold tailWord_772196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082150955236623711180221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18776201273648831614906961 14082150955236623711180221)
  ·
    refine ⟨5280806608213733891692583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14082150955236623711180221 5280806608213733891692583)
    ·
      refine ⟨7921209912320600837538875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5280806608213733891692583 7921209912320600837538875)
      ·
        refine ⟨11881814868480901256308313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921209912320600837538875 11881814868480901256308313)
        ·
          refine ⟨8911361151360675942231235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11881814868480901256308313 8911361151360675942231235)
          ·
            refine ⟨13367041727041013913346853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8911361151360675942231235 13367041727041013913346853)
            ·
              refine ⟨2506320323820190108752535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13367041727041013913346853 2506320323820190108752535)
              ·
                refine ⟨3759480485730285163128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506320323820190108752535 3759480485730285163128803)
                ·
                  refine ⟨5639220728595427744693205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759480485730285163128803 5639220728595427744693205)
                  ·
                    refine ⟨132169235826455337766247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5639220728595427744693205 132169235826455337766247)
                    ·
                      rfl

theorem cell23_772196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_772196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772196 prefixEnd_772196 := by exact prefixLift 772196
  have htrace : WordTrace (prefixWord ++ tailWord_772196) baseStart_772196 baseEnd_772196 := by
    simpa [prefixWord, tailWord_772196, baseEnd_772196] using wordTrace_append hprefix tailTrace_772196
  have hstable : (prefixWord ++ tailWord_772196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772196).length < 2 ^ (prefixWord ++ tailWord_772196).sum := by decide
  have hdescent : baseEnd_772196 < baseStart_772196 := by decide
  rcases family_descends (prefixWord ++ tailWord_772196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772233 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 1, 6, 2]
def baseStart_772233 : Nat := 118140960795 + 772233 * 2 ^ 59
def prefixEnd_772233 : Nat := 4983230072969 + 3 ^ 40 * 772233 * 2
def baseEnd_772233 : Nat := 396526706263582368536071

theorem tailTrace_772233 : CollatzResearch.WordTrace tailWord_772233 prefixEnd_772233 396526706263582368536071 := by
  unfold tailWord_772233
  simp only [CollatzResearch.WordTrace]
  refine ⟨28165651411339202741457353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18777100940892801827638235 28165651411339202741457353)
  ·
    refine ⟨21124238558504402056093015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28165651411339202741457353 21124238558504402056093015)
    ·
      refine ⟨31686357837756603084139523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21124238558504402056093015 31686357837756603084139523)
      ·
        refine ⟨47529536756634904626209285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31686357837756603084139523 47529536756634904626209285)
        ·
          refine ⟨8911788141869044617414241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47529536756634904626209285 8911788141869044617414241)
          ·
            refine ⟨6683841106401783463060681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8911788141869044617414241 6683841106401783463060681)
            ·
              refine ⟨5012880829801337597295511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683841106401783463060681 5012880829801337597295511)
              ·
                refine ⟨7519321244702006395943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012880829801337597295511 7519321244702006395943267)
                ·
                  refine ⟨11278981867053009593914901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519321244702006395943267 11278981867053009593914901)
                  ·
                    refine ⟨528702275018109824714761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11278981867053009593914901 528702275018109824714761)
                    ·
                      refine ⟨396526706263582368536071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528702275018109824714761 396526706263582368536071)
                      ·
                        rfl

theorem cell23_772233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6, 2].length) (baseStart_772233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772233 prefixEnd_772233 := by exact prefixLift 772233
  have htrace : WordTrace (prefixWord ++ tailWord_772233) baseStart_772233 baseEnd_772233 := by
    simpa [prefixWord, tailWord_772233, baseEnd_772233] using wordTrace_append hprefix tailTrace_772233
  have hstable : (prefixWord ++ tailWord_772233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772233).length < 2 ^ (prefixWord ++ tailWord_772233).sum := by decide
  have hdescent : baseEnd_772233 < baseStart_772233 := by decide
  rcases family_descends (prefixWord ++ tailWord_772233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772296 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_772296 : Nat := 118140960795 + 772296 * 2 ^ 59
def prefixEnd_772296 : Nat := 4983230072969 + 3 ^ 40 * 772296 * 2
def baseEnd_772296 : Nat := 396559055544815622048281

theorem tailTrace_772296 : CollatzResearch.WordTrace tailWord_772296 prefixEnd_772296 396559055544815622048281 := by
  unfold tailWord_772296
  simp only [CollatzResearch.WordTrace]
  refine ⟨14083974605055482250500371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18778632806740643000667161 14083974605055482250500371)
  ·
    refine ⟨21125961907583223375750557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14083974605055482250500371 21125961907583223375750557)
    ·
      refine ⟨7922235715343708765906459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21125961907583223375750557 7922235715343708765906459)
      ·
        refine ⟨11883353573015563148859689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922235715343708765906459 11883353573015563148859689)
        ·
          refine ⟨8912515179761672361644767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11883353573015563148859689 8912515179761672361644767)
          ·
            refine ⟨13368772769642508542467151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912515179761672361644767 13368772769642508542467151)
            ·
              refine ⟨20053159154463762813700727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368772769642508542467151 20053159154463762813700727)
              ·
                refine ⟨30079738731695644220551091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20053159154463762813700727 30079738731695644220551091)
                ·
                  refine ⟨45119608097543466330826637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30079738731695644220551091 45119608097543466330826637)
                  ·
                    refine ⟨16919853036578799874059989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45119608097543466330826637 16919853036578799874059989)
                    ·
                      refine ⟨396559055544815622048281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 16919853036578799874059989 396559055544815622048281)
                      ·
                        rfl

theorem cell23_772296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_772296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772296 prefixEnd_772296 := by exact prefixLift 772296
  have htrace : WordTrace (prefixWord ++ tailWord_772296) baseStart_772296 baseEnd_772296 := by
    simpa [prefixWord, tailWord_772296, baseEnd_772296] using wordTrace_append hprefix tailTrace_772296
  have hstable : (prefixWord ++ tailWord_772296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772296).length < 2 ^ (prefixWord ++ tailWord_772296).sum := by decide
  have hdescent : baseEnd_772296 < baseStart_772296 := by decide
  rcases family_descends (prefixWord ++ tailWord_772296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772303 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 1, 5]
def baseStart_772303 : Nat := 118140960795 + 772303 * 2 ^ 59
def prefixEnd_772303 : Nat := 4983230072969 + 3 ^ 40 * 772303 * 2
def baseEnd_772303 : Nat := 132187549969799031553583

theorem tailTrace_772303 : CollatzResearch.WordTrace tailWord_772303 prefixEnd_772303 132187549969799031553583 := by
  unfold tailWord_772303
  simp only [CollatzResearch.WordTrace]
  refine ⟨28168204521085604696505563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18778803014057069797670375 28168204521085604696505563)
  ·
    refine ⟨42252306781628407044758345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28168204521085604696505563 42252306781628407044758345)
    ·
      refine ⟨31689230086221305283568759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42252306781628407044758345 31689230086221305283568759)
      ·
        refine ⟨47533845129331957925353139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31689230086221305283568759 47533845129331957925353139)
        ·
          refine ⟨71300767693997936888029709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47533845129331957925353139 71300767693997936888029709)
          ·
            refine ⟨26737787885249226333011141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71300767693997936888029709 26737787885249226333011141)
            ·
              refine ⟨5013335228484229937439589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26737787885249226333011141 5013335228484229937439589)
              ·
                refine ⟨940000355340793113269923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5013335228484229937439589 940000355340793113269923)
                ·
                  refine ⟨1410000533011189669904885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940000355340793113269923 1410000533011189669904885)
                  ·
                    refine ⟨132187549969799031553583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410000533011189669904885 132187549969799031553583)
                    ·
                      rfl

theorem cell23_772303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_772303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772303 prefixEnd_772303 := by exact prefixLift 772303
  have htrace : WordTrace (prefixWord ++ tailWord_772303) baseStart_772303 baseEnd_772303 := by
    simpa [prefixWord, tailWord_772303, baseEnd_772303] using wordTrace_append hprefix tailTrace_772303
  have hstable : (prefixWord ++ tailWord_772303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772303).length < 2 ^ (prefixWord ++ tailWord_772303).sum := by decide
  have hdescent : baseEnd_772303 < baseStart_772303 := by decide
  rcases family_descends (prefixWord ++ tailWord_772303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772353 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_772353 : Nat := 118140960795 + 772353 * 2 ^ 59
def prefixEnd_772353 : Nat := 4983230072969 + 3 ^ 40 * 772353 * 2
def baseEnd_772353 : Nat := 396588323942121899035519

theorem tailTrace_772353 : CollatzResearch.WordTrace tailWord_772353 prefixEnd_772353 396588323942121899035519 := by
  unfold tailWord_772353
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170028170904463235825713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18780018780602975490550475 28170028170904463235825713)
  ·
    refine ⟨21127521128178347426869285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28170028170904463235825713 21127521128178347426869285)
    ·
      refine ⟨3961410211533440142537991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21127521128178347426869285 3961410211533440142537991)
      ·
        refine ⟨5942115317300160213806987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961410211533440142537991 5942115317300160213806987)
        ·
          refine ⟨8913172975950240320710481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942115317300160213806987 8913172975950240320710481)
          ·
            refine ⟨6684879731962680240532861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8913172975950240320710481 6684879731962680240532861)
            ·
              refine ⟨2506829899486005090199823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6684879731962680240532861 2506829899486005090199823)
              ·
                refine ⟨3760244849229007635299735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506829899486005090199823 3760244849229007635299735)
                ·
                  refine ⟨5640367273843511452949603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760244849229007635299735 5640367273843511452949603)
                  ·
                    refine ⟨8460550910765267179424405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5640367273843511452949603 8460550910765267179424405)
                    ·
                      refine ⟨396588323942121899035519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8460550910765267179424405 396588323942121899035519)
                      ·
                        rfl

theorem cell23_772353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_772353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772353 prefixEnd_772353 := by exact prefixLift 772353
  have htrace : WordTrace (prefixWord ++ tailWord_772353) baseStart_772353 baseEnd_772353 := by
    simpa [prefixWord, tailWord_772353, baseEnd_772353] using wordTrace_append hprefix tailTrace_772353
  have hstable : (prefixWord ++ tailWord_772353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772353).length < 2 ^ (prefixWord ++ tailWord_772353).sum := by decide
  have hdescent : baseEnd_772353 < baseStart_772353 := by decide
  rcases family_descends (prefixWord ++ tailWord_772353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772397 : List Nat := [1, 5, 3, 1, 2, 1, 2, 8]
def baseStart_772397 : Nat := 118140960795 + 772397 * 2 ^ 59
def prefixEnd_772397 : Nat := 4983230072969 + 3 ^ 40 * 772397 * 2
def baseEnd_772397 : Nat := 14689293225589619514271

theorem tailTrace_772397 : CollatzResearch.WordTrace tailWord_772397 prefixEnd_772397 14689293225589619514271 := by
  unfold tailWord_772397
  simp only [CollatzResearch.WordTrace]
  refine ⟨28171632982745058750427445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18781088655163372500284963 28171632982745058750427445)
  ·
    refine ⟨2641090592132349257852573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28171632982745058750427445 2641090592132349257852573)
    ·
      refine ⟨990408972049630971694715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2641090592132349257852573 990408972049630971694715)
      ·
        refine ⟨1485613458074446457542073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990408972049630971694715 1485613458074446457542073)
        ·
          refine ⟨1114210093555834843156555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485613458074446457542073 1114210093555834843156555)
          ·
            refine ⟨1671315140333752264734833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114210093555834843156555 1671315140333752264734833)
            ·
              refine ⟨1253486355250314198551125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671315140333752264734833 1253486355250314198551125)
              ·
                refine ⟨14689293225589619514271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1253486355250314198551125 14689293225589619514271)
                ·
                  rfl

theorem cell23_772397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 8].length) (baseStart_772397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772397 prefixEnd_772397 := by exact prefixLift 772397
  have htrace : WordTrace (prefixWord ++ tailWord_772397) baseStart_772397 baseEnd_772397 := by
    simpa [prefixWord, tailWord_772397, baseEnd_772397] using wordTrace_append hprefix tailTrace_772397
  have hstable : (prefixWord ++ tailWord_772397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772397).length < 2 ^ (prefixWord ++ tailWord_772397).sum := by decide
  have hdescent : baseEnd_772397 < baseStart_772397 := by decide
  rcases family_descends (prefixWord ++ tailWord_772397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772401 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 2, 4]
def baseStart_772401 : Nat := 118140960795 + 772401 * 2 ^ 59
def prefixEnd_772401 : Nat := 4983230072969 + 3 ^ 40 * 772401 * 2
def baseEnd_772401 : Nat := 132204323671179237078433

theorem tailTrace_772401 : CollatzResearch.WordTrace tailWord_772401 prefixEnd_772401 132204323671179237078433 := by
  unfold tailWord_772401
  simp only [CollatzResearch.WordTrace]
  refine ⟨28171778874730567433573057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18781185916487044955715371 28171778874730567433573057)
  ·
    refine ⟨21128834156047925575179793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28171778874730567433573057 21128834156047925575179793)
    ·
      refine ⟨15846625617035944181384845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21128834156047925575179793 15846625617035944181384845)
      ·
        refine ⟨5942484606388479068019317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15846625617035944181384845 5942484606388479068019317)
        ·
          refine ⟨557107931848919912626811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5942484606388479068019317 557107931848919912626811)
          ·
            refine ⟨835661897773379868940217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557107931848919912626811 835661897773379868940217)
            ·
              refine ⟨626746423330034901705163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835661897773379868940217 626746423330034901705163)
              ·
                refine ⟨940119634995052352557745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 626746423330034901705163 940119634995052352557745)
                ·
                  refine ⟨705089726246289264418309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 940119634995052352557745 705089726246289264418309)
                  ·
                    refine ⟨132204323671179237078433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705089726246289264418309 132204323671179237078433)
                    ·
                      rfl

theorem cell23_772401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_772401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772401 prefixEnd_772401 := by exact prefixLift 772401
  have htrace : WordTrace (prefixWord ++ tailWord_772401) baseStart_772401 baseEnd_772401 := by
    simpa [prefixWord, tailWord_772401, baseEnd_772401] using wordTrace_append hprefix tailTrace_772401
  have hstable : (prefixWord ++ tailWord_772401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772401).length < 2 ^ (prefixWord ++ tailWord_772401).sum := by decide
  have hdescent : baseEnd_772401 < baseStart_772401 := by decide
  rcases family_descends (prefixWord ++ tailWord_772401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772447 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 4, 2, 2]
def baseStart_772447 : Nat := 118140960795 + 772447 * 2 ^ 59
def prefixEnd_772447 : Nat := 4983230072969 + 3 ^ 40 * 772447 * 2
def baseEnd_772447 : Nat := 396636591123644531260087

theorem tailTrace_772447 : CollatzResearch.WordTrace tailWord_772447 prefixEnd_772447 396636591123644531260087 := by
  unfold tailWord_772447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28173456632563917289747595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18782304421709278193165063 28173456632563917289747595)
  ·
    refine ⟨42260184948845875934621393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28173456632563917289747595 42260184948845875934621393)
    ·
      refine ⟨31695138711634406950966045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42260184948845875934621393 31695138711634406950966045)
      ·
        refine ⟨11885677016862902606612267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31695138711634406950966045 11885677016862902606612267)
        ·
          refine ⟨17828515525294353909918401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11885677016862902606612267 17828515525294353909918401)
          ·
            refine ⟨13371386643970765432438801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17828515525294353909918401 13371386643970765432438801)
            ·
              refine ⟨10028539982978074074329101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13371386643970765432438801 10028539982978074074329101)
              ·
                refine ⟨3760702493616777777873413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10028539982978074074329101 3760702493616777777873413)
                ·
                  refine ⟨705131717553145833351265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3760702493616777777873413 705131717553145833351265)
                  ·
                    refine ⟨528848788164859375013449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705131717553145833351265 528848788164859375013449)
                    ·
                      refine ⟨396636591123644531260087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528848788164859375013449 396636591123644531260087)
                      ·
                        rfl

theorem cell23_772447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_772447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772447 prefixEnd_772447 := by exact prefixLift 772447
  have htrace : WordTrace (prefixWord ++ tailWord_772447) baseStart_772447 baseEnd_772447 := by
    simpa [prefixWord, tailWord_772447, baseEnd_772447] using wordTrace_append hprefix tailTrace_772447
  have hstable : (prefixWord ++ tailWord_772447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772447).length < 2 ^ (prefixWord ++ tailWord_772447).sum := by decide
  have hdescent : baseEnd_772447 < baseStart_772447 := by decide
  rcases family_descends (prefixWord ++ tailWord_772447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772464 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2]
def baseStart_772464 : Nat := 118140960795 + 772464 * 2 ^ 59
def prefixEnd_772464 : Nat := 4983230072969 + 3 ^ 40 * 772464 * 2
def baseEnd_772464 : Nat := 396645320294770964747509

theorem tailTrace_772464 : CollatzResearch.WordTrace tailWord_772464 prefixEnd_772464 396645320294770964747509 := by
  unfold tailWord_772464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087038336751164596558223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18782717782334886128744297 14087038336751164596558223)
  ·
    refine ⟨21130557505126746894837335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14087038336751164596558223 21130557505126746894837335)
    ·
      refine ⟨31695836257690120342256003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21130557505126746894837335 31695836257690120342256003)
      ·
        refine ⟨47543754386535180513384005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31695836257690120342256003 47543754386535180513384005)
        ·
          refine ⟨8914453947475346346259501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47543754386535180513384005 8914453947475346346259501)
          ·
            refine ⟨3342920230303254879847313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8914453947475346346259501 3342920230303254879847313)
            ·
              refine ⟨2507190172727441159885485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3342920230303254879847313 2507190172727441159885485)
              ·
                refine ⟨940196314772790434957057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2507190172727441159885485 940196314772790434957057)
                ·
                  refine ⟨705147236079592826217793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 940196314772790434957057 705147236079592826217793)
                  ·
                    refine ⟨528860427059694619663345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705147236079592826217793 528860427059694619663345)
                    ·
                      refine ⟨396645320294770964747509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528860427059694619663345 396645320294770964747509)
                      ·
                        rfl

theorem cell23_772464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 2, 2, 2].length) (baseStart_772464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772464 prefixEnd_772464 := by exact prefixLift 772464
  have htrace : WordTrace (prefixWord ++ tailWord_772464) baseStart_772464 baseEnd_772464 := by
    simpa [prefixWord, tailWord_772464, baseEnd_772464] using wordTrace_append hprefix tailTrace_772464
  have hstable : (prefixWord ++ tailWord_772464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772464).length < 2 ^ (prefixWord ++ tailWord_772464).sum := by decide
  have hdescent : baseEnd_772464 < baseStart_772464 := by decide
  rcases family_descends (prefixWord ++ tailWord_772464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772487 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 5]
def baseStart_772487 : Nat := 118140960795 + 772487 * 2 ^ 59
def prefixEnd_772487 : Nat := 4983230072969 + 3 ^ 40 * 772487 * 2
def baseEnd_772487 : Nat := 44073014483313819417767

theorem tailTrace_772487 : CollatzResearch.WordTrace tailWord_772487 prefixEnd_772487 44073014483313819417767 := by
  unfold tailWord_772487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28174915552419004121203715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18783277034946002747469143 28174915552419004121203715)
  ·
    refine ⟨42262373328628506181805573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28174915552419004121203715 42262373328628506181805573)
    ·
      refine ⟨7924194999117844909088545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42262373328628506181805573 7924194999117844909088545)
      ·
        refine ⟨5943146249338383681816409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7924194999117844909088545 5943146249338383681816409)
        ·
          refine ⟨4457359687003787761362307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943146249338383681816409 4457359687003787761362307)
          ·
            refine ⟨6686039530505681642043461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457359687003787761362307 6686039530505681642043461)
            ·
              refine ⟨1253632411969815307883149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6686039530505681642043461 1253632411969815307883149)
              ·
                refine ⟨470112154488680740456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253632411969815307883149 470112154488680740456181)
                ·
                  refine ⟨44073014483313819417767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470112154488680740456181 44073014483313819417767)
                  ·
                    rfl

theorem cell23_772487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 5].length) (baseStart_772487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772487 prefixEnd_772487 := by exact prefixLift 772487
  have htrace : WordTrace (prefixWord ++ tailWord_772487) baseStart_772487 baseEnd_772487 := by
    simpa [prefixWord, tailWord_772487, baseEnd_772487] using wordTrace_append hprefix tailTrace_772487
  have hstable : (prefixWord ++ tailWord_772487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772487).length < 2 ^ (prefixWord ++ tailWord_772487).sum := by decide
  have hdescent : baseEnd_772487 < baseStart_772487 := by decide
  rcases family_descends (prefixWord ++ tailWord_772487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772564 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_772564 : Nat := 118140960795 + 772564 * 2 ^ 59
def prefixEnd_772564 : Nat := 4983230072969 + 3 ^ 40 * 772564 * 2
def baseEnd_772564 : Nat := 132232222786740191165683

theorem tailTrace_772564 : CollatzResearch.WordTrace tailWord_772564 prefixEnd_772564 132232222786740191165683 := by
  unfold tailWord_772564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14088861986570023135878373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18785149315426697514504497 14088861986570023135878373)
  ·
    refine ⟨2641661622481879337977195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14088861986570023135878373 2641661622481879337977195)
    ·
      refine ⟨3962492433722819006965793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2641661622481879337977195 3962492433722819006965793)
      ·
        refine ⟨2971869325292114255224345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3962492433722819006965793 2971869325292114255224345)
        ·
          refine ⟨2228901993969085691418259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2971869325292114255224345 2228901993969085691418259)
          ·
            refine ⟨3343352990953628537127389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228901993969085691418259 3343352990953628537127389)
            ·
              refine ⟨1253757371607610701422771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3343352990953628537127389 1253757371607610701422771)
              ·
                refine ⟨1880636057411416052134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253757371607610701422771 1880636057411416052134157)
                ·
                  refine ⟨705238521529281019550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1880636057411416052134157 705238521529281019550309)
                  ·
                    refine ⟨132232222786740191165683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705238521529281019550309 132232222786740191165683)
                    ·
                      rfl

theorem cell23_772564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_772564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772564 prefixEnd_772564 := by exact prefixLift 772564
  have htrace : WordTrace (prefixWord ++ tailWord_772564) baseStart_772564 baseEnd_772564 := by
    simpa [prefixWord, tailWord_772564, baseEnd_772564] using wordTrace_append hprefix tailTrace_772564
  have hstable : (prefixWord ++ tailWord_772564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772564).length < 2 ^ (prefixWord ++ tailWord_772564).sum := by decide
  have hdescent : baseEnd_772564 < baseStart_772564 := by decide
  rcases family_descends (prefixWord ++ tailWord_772564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772587 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 3]
def baseStart_772587 : Nat := 118140960795 + 772587 * 2 ^ 59
def prefixEnd_772587 : Nat := 4983230072969 + 3 ^ 40 * 772587 * 2
def baseEnd_772587 : Nat := 396708478415273983509443

theorem tailTrace_772587 : CollatzResearch.WordTrace tailWord_772587 prefixEnd_772587 396708478415273983509443 := by
  unfold tailWord_772587
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178562852056721199844015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18785708568037814133229343 28178562852056721199844015)
  ·
    refine ⟨42267844278085081799766023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28178562852056721199844015 42267844278085081799766023)
    ·
      refine ⟨63401766417127622699649035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42267844278085081799766023 63401766417127622699649035)
      ·
        refine ⟨95102649625691434049473553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63401766417127622699649035 95102649625691434049473553)
        ·
          refine ⟨71326987219268575537105165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95102649625691434049473553 71326987219268575537105165)
          ·
            refine ⟨26747620207225715826414437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71326987219268575537105165 26747620207225715826414437)
            ·
              refine ⟨5015178788854821717452707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26747620207225715826414437 5015178788854821717452707)
              ·
                refine ⟨7522768183282232576179061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015178788854821717452707 7522768183282232576179061)
                ·
                  refine ⟨705259517182709304016787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7522768183282232576179061 705259517182709304016787)
                  ·
                    refine ⟨1057889275774063956025181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 705259517182709304016787 1057889275774063956025181)
                    ·
                      refine ⟨396708478415273983509443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1057889275774063956025181 396708478415273983509443)
                      ·
                        rfl

theorem cell23_772587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 3].length) (baseStart_772587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772587 prefixEnd_772587 := by exact prefixLift 772587
  have htrace : WordTrace (prefixWord ++ tailWord_772587) baseStart_772587 baseEnd_772587 := by
    simpa [prefixWord, tailWord_772587, baseEnd_772587] using wordTrace_append hprefix tailTrace_772587
  have hstable : (prefixWord ++ tailWord_772587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772587).length < 2 ^ (prefixWord ++ tailWord_772587).sum := by decide
  have hdescent : baseEnd_772587 < baseStart_772587 := by decide
  rcases family_descends (prefixWord ++ tailWord_772587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772615 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 1, 4]
def baseStart_772615 : Nat := 118140960795 + 772615 * 2 ^ 59
def prefixEnd_772615 : Nat := 4983230072969 + 3 ^ 40 * 772615 * 2
def baseEnd_772615 : Nat := 132240951957866624653105

theorem tailTrace_772615 : CollatzResearch.WordTrace tailWord_772615 prefixEnd_772615 132240951957866624653105 := by
  unfold tailWord_772615
  simp only [CollatzResearch.WordTrace]
  refine ⟨28179584095955281981863299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18786389397303521321242199 28179584095955281981863299)
  ·
    refine ⟨42269376143932922972794949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28179584095955281981863299 42269376143932922972794949)
    ·
      refine ⟨7925508026987423057399053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42269376143932922972794949 7925508026987423057399053)
      ·
        refine ⟨2972065510120283646524645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7925508026987423057399053 2972065510120283646524645)
        ·
          refine ⟨557262283147553183723371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2972065510120283646524645 557262283147553183723371)
          ·
            refine ⟨835893424721329775585057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557262283147553183723371 835893424721329775585057)
            ·
              refine ⟨626920068540997331688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 835893424721329775585057 626920068540997331688793)
              ·
                refine ⟨470190051405747998766595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 626920068540997331688793 470190051405747998766595)
                ·
                  refine ⟨705285077108621998149893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470190051405747998766595 705285077108621998149893)
                  ·
                    refine ⟨132240951957866624653105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705285077108621998149893 132240951957866624653105)
                    ·
                      rfl

theorem cell23_772615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_772615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772615 prefixEnd_772615 := by exact prefixLift 772615
  have htrace : WordTrace (prefixWord ++ tailWord_772615) baseStart_772615 baseEnd_772615 := by
    simpa [prefixWord, tailWord_772615, baseEnd_772615] using wordTrace_append hprefix tailTrace_772615
  have hstable : (prefixWord ++ tailWord_772615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772615).length < 2 ^ (prefixWord ++ tailWord_772615).sum := by decide
  have hdescent : baseEnd_772615 < baseStart_772615 := by decide
  rcases family_descends (prefixWord ++ tailWord_772615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772637 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_772637 : Nat := 118140960795 + 772637 * 2 ^ 59
def prefixEnd_772637 : Nat := 4983230072969 + 3 ^ 40 * 772637 * 2
def baseEnd_772637 : Nat := 132244717482666262628071

theorem tailTrace_772637 : CollatzResearch.WordTrace tailWord_772637 prefixEnd_772637 132244717482666262628071 := by
  unfold tailWord_772637
  simp only [CollatzResearch.WordTrace]
  refine ⟨28180386501875579739164165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18786924334583719826109443 28180386501875579739164165)
  ·
    refine ⟨5283822469101671201093281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28180386501875579739164165 5283822469101671201093281)
    ·
      refine ⟨3962866851826253400819961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5283822469101671201093281 3962866851826253400819961)
      ·
        refine ⟨2972150138869690050614971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3962866851826253400819961 2972150138869690050614971)
        ·
          refine ⟨4458225208304535075922457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972150138869690050614971 4458225208304535075922457)
          ·
            refine ⟨3343668906228401306941843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4458225208304535075922457 3343668906228401306941843)
            ·
              refine ⟨5015503359342601960412765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343668906228401306941843 5015503359342601960412765)
              ·
                refine ⟨1880813759753475735154787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5015503359342601960412765 1880813759753475735154787)
                ·
                  refine ⟨2821220639630213602732181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880813759753475735154787 2821220639630213602732181)
                  ·
                    refine ⟨132244717482666262628071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2821220639630213602732181 132244717482666262628071)
                    ·
                      rfl

theorem cell23_772637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_772637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772637 prefixEnd_772637 := by exact prefixLift 772637
  have htrace : WordTrace (prefixWord ++ tailWord_772637) baseStart_772637 baseEnd_772637 := by
    simpa [prefixWord, tailWord_772637, baseEnd_772637] using wordTrace_append hprefix tailTrace_772637
  have hstable : (prefixWord ++ tailWord_772637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772637).length < 2 ^ (prefixWord ++ tailWord_772637).sum := by decide
  have hdescent : baseEnd_772637 < baseStart_772637 := by decide
  rcases family_descends (prefixWord ++ tailWord_772637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772648 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_772648 : Nat := 118140960795 + 772648 * 2 ^ 59
def prefixEnd_772648 : Nat := 4983230072969 + 3 ^ 40 * 772648 * 2
def baseEnd_772648 : Nat := 396739800735198244846663

theorem tailTrace_772648 : CollatzResearch.WordTrace tailWord_772648 prefixEnd_772648 396739800735198244846663 := by
  unfold tailWord_772648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090393852417864308907299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18787191803223819078543065 14090393852417864308907299)
  ·
    refine ⟨21135590778626796463360949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090393852417864308907299 21135590778626796463360949)
    ·
      refine ⟨1981461635496262168440089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21135590778626796463360949 1981461635496262168440089)
      ·
        refine ⟨1486096226622196626330067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1981461635496262168440089 1486096226622196626330067)
        ·
          refine ⟨2229144339933294939495101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486096226622196626330067 2229144339933294939495101)
          ·
            refine ⟨835929127474985602310663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2229144339933294939495101 835929127474985602310663)
            ·
              refine ⟨1253893691212478403465995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835929127474985602310663 1253893691212478403465995)
              ·
                refine ⟨1880840536818717605198993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253893691212478403465995 1880840536818717605198993)
                ·
                  refine ⟨1410630402614038203899245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880840536818717605198993 1410630402614038203899245)
                  ·
                    refine ⟨528986400980264326462217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410630402614038203899245 528986400980264326462217)
                    ·
                      refine ⟨396739800735198244846663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 528986400980264326462217 396739800735198244846663)
                      ·
                        rfl

theorem cell23_772648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_772648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772648 prefixEnd_772648 := by exact prefixLift 772648
  have htrace : WordTrace (prefixWord ++ tailWord_772648) baseStart_772648 baseEnd_772648 := by
    simpa [prefixWord, tailWord_772648, baseEnd_772648] using wordTrace_append hprefix tailTrace_772648
  have hstable : (prefixWord ++ tailWord_772648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772648).length < 2 ^ (prefixWord ++ tailWord_772648).sum := by decide
  have hdescent : baseEnd_772648 < baseStart_772648 := by decide
  rcases family_descends (prefixWord ++ tailWord_772648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772657 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_772657 : Nat := 118140960795 + 772657 * 2 ^ 59
def prefixEnd_772657 : Nat := 4983230072969 + 3 ^ 40 * 772657 * 2
def baseEnd_772657 : Nat := 396744422061088709634121

theorem tailTrace_772657 : CollatzResearch.WordTrace tailWord_772657 prefixEnd_772657 396744422061088709634121 := by
  unfold tailWord_772657
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181115961803123154892225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18787410641202082103261483 28181115961803123154892225)
  ·
    refine ⟨21135836971352342366169169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28181115961803123154892225 21135836971352342366169169)
    ·
      refine ⟨15851877728514256774626877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21135836971352342366169169 15851877728514256774626877)
      ·
        refine ⟨5944454148192846290485079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15851877728514256774626877 5944454148192846290485079)
        ·
          refine ⟨8916681222289269435727619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944454148192846290485079 8916681222289269435727619)
          ·
            refine ⟨13375021833433904153591429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916681222289269435727619 13375021833433904153591429)
            ·
              refine ⟨2507816593768857028798393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13375021833433904153591429 2507816593768857028798393)
              ·
                refine ⟨1880862445326642771598795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507816593768857028798393 1880862445326642771598795)
                ·
                  refine ⟨2821293667989964157398193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880862445326642771598795 2821293667989964157398193)
                  ·
                    refine ⟨2115970250992473118048645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2821293667989964157398193 2115970250992473118048645)
                    ·
                      refine ⟨396744422061088709634121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2115970250992473118048645 396744422061088709634121)
                      ·
                        rfl

theorem cell23_772657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_772657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772657 prefixEnd_772657 := by exact prefixLift 772657
  have htrace : WordTrace (prefixWord ++ tailWord_772657) baseStart_772657 baseEnd_772657 := by
    simpa [prefixWord, tailWord_772657, baseEnd_772657] using wordTrace_append hprefix tailTrace_772657
  have hstable : (prefixWord ++ tailWord_772657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772657).length < 2 ^ (prefixWord ++ tailWord_772657).sum := by decide
  have hdescent : baseEnd_772657 < baseStart_772657 := by decide
  rcases family_descends (prefixWord ++ tailWord_772657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772664 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3]
def baseStart_772664 : Nat := 118140960795 + 772664 * 2 ^ 59
def prefixEnd_772664 : Nat := 4983230072969 + 3 ^ 40 * 772664 * 2
def baseEnd_772664 : Nat := 396748016425670182246589

theorem tailTrace_772664 : CollatzResearch.WordTrace tailWord_772664 prefixEnd_772664 396748016425670182246589 := by
  unfold tailWord_772664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090685636388881675198523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18787580848518508900264697 14090685636388881675198523)
  ·
    refine ⟨21136028454583322512797785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090685636388881675198523 21136028454583322512797785)
    ·
      refine ⟨15852021340937491884598339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21136028454583322512797785 15852021340937491884598339)
      ·
        refine ⟨23778032011406237826897509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15852021340937491884598339 23778032011406237826897509)
        ·
          refine ⟨4458381002138669592543283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23778032011406237826897509 4458381002138669592543283)
          ·
            refine ⟨6687571503208004388814925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458381002138669592543283 6687571503208004388814925)
            ·
              refine ⟨2507839313703001645805597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6687571503208004388814925 2507839313703001645805597)
              ·
                refine ⟨940439742638625617177099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2507839313703001645805597 940439742638625617177099)
                ·
                  refine ⟨1410659613957938425765649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940439742638625617177099 1410659613957938425765649)
                  ·
                    refine ⟨1057994710468453819324237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410659613957938425765649 1057994710468453819324237)
                    ·
                      refine ⟨396748016425670182246589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1057994710468453819324237 396748016425670182246589)
                      ·
                        rfl

theorem cell23_772664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_772664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772664 prefixEnd_772664 := by exact prefixLift 772664
  have htrace : WordTrace (prefixWord ++ tailWord_772664) baseStart_772664 baseEnd_772664 := by
    simpa [prefixWord, tailWord_772664, baseEnd_772664] using wordTrace_append hprefix tailTrace_772664
  have hstable : (prefixWord ++ tailWord_772664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772664).length < 2 ^ (prefixWord ++ tailWord_772664).sum := by decide
  have hdescent : baseEnd_772664 < baseStart_772664 := by decide
  rcases family_descends (prefixWord ++ tailWord_772664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772680 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 9]
def baseStart_772680 : Nat := 118140960795 + 772680 * 2 ^ 59
def prefixEnd_772680 : Nat := 4983230072969 + 3 ^ 40 * 772680 * 2
def baseEnd_772680 : Nat := 132252077372047373215505

theorem tailTrace_772680 : CollatzResearch.WordTrace tailWord_772680 prefixEnd_772680 132252077372047373215505 := by
  unfold tailWord_772680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090977420359899041489747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18787969893813198721986329 14090977420359899041489747)
  ·
    refine ⟨21136466130539848562234621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14090977420359899041489747 21136466130539848562234621)
    ·
      refine ⟨7926174798952443210837983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21136466130539848562234621 7926174798952443210837983)
      ·
        refine ⟨11889262198428664816256975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926174798952443210837983 11889262198428664816256975)
        ·
          refine ⟨17833893297642997224385463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11889262198428664816256975 17833893297642997224385463)
          ·
            refine ⟨26750839946464495836578195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833893297642997224385463 26750839946464495836578195)
            ·
              refine ⟨40126259919696743754867293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26750839946464495836578195 40126259919696743754867293)
              ·
                refine ⟨15047347469886278908075235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40126259919696743754867293 15047347469886278908075235)
                ·
                  refine ⟨22571021204829418362112853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15047347469886278908075235 22571021204829418362112853)
                  ·
                    refine ⟨132252077372047373215505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22571021204829418362112853 132252077372047373215505)
                    ·
                      rfl

theorem cell23_772680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_772680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772680 prefixEnd_772680 := by exact prefixLift 772680
  have htrace : WordTrace (prefixWord ++ tailWord_772680) baseStart_772680 baseEnd_772680 := by
    simpa [prefixWord, tailWord_772680, baseEnd_772680] using wordTrace_append hprefix tailTrace_772680
  have hstable : (prefixWord ++ tailWord_772680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772680).length < 2 ^ (prefixWord ++ tailWord_772680).sum := by decide
  have hdescent : baseEnd_772680 < baseStart_772680 := by decide
  rcases family_descends (prefixWord ++ tailWord_772680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772704 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2]
def baseStart_772704 : Nat := 118140960795 + 772704 * 2 ^ 59
def prefixEnd_772704 : Nat := 4983230072969 + 3 ^ 40 * 772704 * 2
def baseEnd_772704 : Nat := 396768555651850025746405

theorem tailTrace_772704 : CollatzResearch.WordTrace tailWord_772704 prefixEnd_772704 396768555651850025746405 := by
  unfold tailWord_772704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091415096316425090926583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18788553461755233454568777 14091415096316425090926583)
  ·
    refine ⟨21137122644474637636389875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14091415096316425090926583 21137122644474637636389875)
    ·
      refine ⟨31705683966711956454584813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21137122644474637636389875 31705683966711956454584813)
      ·
        refine ⟨11889631487516983670469305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31705683966711956454584813 11889631487516983670469305)
        ·
          refine ⟨8917223615637737752851979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11889631487516983670469305 8917223615637737752851979)
          ·
            refine ⟨13375835423456606629277969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917223615637737752851979 13375835423456606629277969)
            ·
              refine ⟨10031876567592454971958477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13375835423456606629277969 10031876567592454971958477)
              ·
                refine ⟨3761953712847170614484429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10031876567592454971958477 3761953712847170614484429)
                ·
                  refine ⟨1410732642317688980431661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3761953712847170614484429 1410732642317688980431661)
                  ·
                    refine ⟨529024740869133367661873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410732642317688980431661 529024740869133367661873)
                    ·
                      refine ⟨396768555651850025746405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529024740869133367661873 396768555651850025746405)
                      ·
                        rfl

theorem cell23_772704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_772704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772704 prefixEnd_772704 := by exact prefixLift 772704
  have htrace : WordTrace (prefixWord ++ tailWord_772704) baseStart_772704 baseEnd_772704 := by
    simpa [prefixWord, tailWord_772704, baseEnd_772704] using wordTrace_append hprefix tailTrace_772704
  have hstable : (prefixWord ++ tailWord_772704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772704).length < 2 ^ (prefixWord ++ tailWord_772704).sum := by decide
  have hdescent : baseEnd_772704 < baseStart_772704 := by decide
  rcases family_descends (prefixWord ++ tailWord_772704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772712 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_772712 : Nat := 118140960795 + 772712 * 2 ^ 59
def prefixEnd_772712 : Nat := 4983230072969 + 3 ^ 40 * 772712 * 2
def baseEnd_772712 : Nat := 396772663497085994446369

theorem tailTrace_772712 : CollatzResearch.WordTrace tailWord_772712 prefixEnd_772712 396772663497085994446369 := by
  unfold tailWord_772712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091560988301933774072195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18788747984402578365429593 14091560988301933774072195)
  ·
    refine ⟨21137341482452900661108293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14091560988301933774072195 21137341482452900661108293)
    ·
      refine ⟨3963251527959918873957805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21137341482452900661108293 3963251527959918873957805)
      ·
        refine ⟨1486219322984969577734177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3963251527959918873957805 1486219322984969577734177)
        ·
          refine ⟨1114664492238727183300633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486219322984969577734177 1114664492238727183300633)
          ·
            refine ⟨835998369179045387475475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114664492238727183300633 835998369179045387475475)
            ·
              refine ⟨1253997553768568081213213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835998369179045387475475 1253997553768568081213213)
              ·
                refine ⟨470249082663213030454955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1253997553768568081213213 470249082663213030454955)
                ·
                  refine ⟨705373623994819545682433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470249082663213030454955 705373623994819545682433)
                  ·
                    refine ⟨529030217996114659261825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705373623994819545682433 529030217996114659261825)
                    ·
                      refine ⟨396772663497085994446369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529030217996114659261825 396772663497085994446369)
                      ·
                        rfl

theorem cell23_772712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_772712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772712 prefixEnd_772712 := by exact prefixLift 772712
  have htrace : WordTrace (prefixWord ++ tailWord_772712) baseStart_772712 baseEnd_772712 := by
    simpa [prefixWord, tailWord_772712, baseEnd_772712] using wordTrace_append hprefix tailTrace_772712
  have hstable : (prefixWord ++ tailWord_772712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772712).length < 2 ^ (prefixWord ++ tailWord_772712).sum := by decide
  have hdescent : baseEnd_772712 < baseStart_772712 := by decide
  rcases family_descends (prefixWord ++ tailWord_772712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772737 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_772737 : Nat := 118140960795 + 772737 * 2 ^ 59
def prefixEnd_772737 : Nat := 4983230072969 + 3 ^ 40 * 772737 * 2
def baseEnd_772737 : Nat := 396785500513448396633753

theorem tailTrace_772737 : CollatzResearch.WordTrace tailWord_772737 prefixEnd_772737 396785500513448396633753 := by
  unfold tailWord_772737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28184033801513296817804465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18789355867675531211869643 28184033801513296817804465)
  ·
    refine ⟨21138025351134972613353349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28184033801513296817804465 21138025351134972613353349)
    ·
      refine ⟨3963379753337807365003753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21138025351134972613353349 3963379753337807365003753)
      ·
        refine ⟨2972534815003355523752815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3963379753337807365003753 2972534815003355523752815)
        ·
          refine ⟨4458802222505033285629223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972534815003355523752815 4458802222505033285629223)
          ·
            refine ⟨6688203333757549928443835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458802222505033285629223 6688203333757549928443835)
            ·
              refine ⟨10032305000636324892665753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688203333757549928443835 10032305000636324892665753)
              ·
                refine ⟨7524228750477243669499315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10032305000636324892665753 7524228750477243669499315)
                ·
                  refine ⟨11286343125715865504248973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7524228750477243669499315 11286343125715865504248973)
                  ·
                    refine ⟨4232378672143449564093365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11286343125715865504248973 4232378672143449564093365)
                    ·
                      refine ⟨396785500513448396633753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4232378672143449564093365 396785500513448396633753)
                      ·
                        rfl

theorem cell23_772737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_772737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772737 prefixEnd_772737 := by exact prefixLift 772737
  have htrace : WordTrace (prefixWord ++ tailWord_772737) baseStart_772737 baseEnd_772737 := by
    simpa [prefixWord, tailWord_772737, baseEnd_772737] using wordTrace_append hprefix tailTrace_772737
  have hstable : (prefixWord ++ tailWord_772737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772737).length < 2 ^ (prefixWord ++ tailWord_772737).sum := by decide
  have hdescent : baseEnd_772737 < baseStart_772737 := by decide
  rcases family_descends (prefixWord ++ tailWord_772737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772751 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 2, 2, 2]
def baseStart_772751 : Nat := 118140960795 + 772751 * 2 ^ 59
def prefixEnd_772751 : Nat := 4983230072969 + 3 ^ 40 * 772751 * 2
def baseEnd_772751 : Nat := 396792689242611341858689

theorem tailTrace_772751 : CollatzResearch.WordTrace tailWord_772751 prefixEnd_772751 396792689242611341858689 := by
  unfold tailWord_772751
  simp only [CollatzResearch.WordTrace]
  refine ⟨28184544423462577208814107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18789696282308384805876071 28184544423462577208814107)
  ·
    refine ⟨42276816635193865813221161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28184544423462577208814107 42276816635193865813221161)
    ·
      refine ⟨31707612476395399359915871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42276816635193865813221161 31707612476395399359915871)
      ·
        refine ⟨47561418714593099039873807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31707612476395399359915871 47561418714593099039873807)
        ·
          refine ⟨71342128071889648559810711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47561418714593099039873807 71342128071889648559810711)
          ·
            refine ⟨107013192107834472839716067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71342128071889648559810711 107013192107834472839716067)
            ·
              refine ⟨160519788161751709259574101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107013192107834472839716067 160519788161751709259574101)
              ·
                refine ⟨940545633760263921442817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 160519788161751709259574101 940545633760263921442817)
                ·
                  refine ⟨705409225320197941082113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 940545633760263921442817 705409225320197941082113)
                  ·
                    refine ⟨529056918990148455811585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705409225320197941082113 529056918990148455811585)
                    ·
                      refine ⟨396792689242611341858689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529056918990148455811585 396792689242611341858689)
                      ·
                        rfl

theorem cell23_772751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2, 2].length) (baseStart_772751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772751 prefixEnd_772751 := by exact prefixLift 772751
  have htrace : WordTrace (prefixWord ++ tailWord_772751) baseStart_772751 baseEnd_772751 := by
    simpa [prefixWord, tailWord_772751, baseEnd_772751] using wordTrace_append hprefix tailTrace_772751
  have hstable : (prefixWord ++ tailWord_772751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772751).length < 2 ^ (prefixWord ++ tailWord_772751).sum := by decide
  have hdescent : baseEnd_772751 < baseStart_772751 := by decide
  rcases family_descends (prefixWord ++ tailWord_772751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772754 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_772754 : Nat := 118140960795 + 772754 * 2 ^ 59
def prefixEnd_772754 : Nat := 4983230072969 + 3 ^ 40 * 772754 * 2
def baseEnd_772754 : Nat := 396794229684574830121175

theorem tailTrace_772754 : CollatzResearch.WordTrace tailWord_772754 prefixEnd_772754 396794229684574830121175 := by
  unfold tailWord_772754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046163460612927180293329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18789769228301139147448877 7046163460612927180293329)
  ·
    refine ⟨5284622595459695385219997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7046163460612927180293329 5284622595459695385219997)
    ·
      refine ⟨1981733473297385769457499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5284622595459695385219997 1981733473297385769457499)
      ·
        refine ⟨2972600209946078654186249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981733473297385769457499 2972600209946078654186249)
        ·
          refine ⟨2229450157459558990639687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2972600209946078654186249 2229450157459558990639687)
          ·
            refine ⟨3344175236189338485959531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229450157459558990639687 3344175236189338485959531)
            ·
              refine ⟨5016262854284007728939297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344175236189338485959531 5016262854284007728939297)
              ·
                refine ⟨3762197140713005796704473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5016262854284007728939297 3762197140713005796704473)
                ·
                  refine ⟨2821647855534754347528355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762197140713005796704473 2821647855534754347528355)
                  ·
                    refine ⟨4232471783302131521292533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2821647855534754347528355 4232471783302131521292533)
                    ·
                      refine ⟨396794229684574830121175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4232471783302131521292533 396794229684574830121175)
                      ·
                        rfl

theorem cell23_772754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_772754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772754 prefixEnd_772754 := by exact prefixLift 772754
  have htrace : WordTrace (prefixWord ++ tailWord_772754) baseStart_772754 baseEnd_772754 := by
    simpa [prefixWord, tailWord_772754, baseEnd_772754] using wordTrace_append hprefix tailTrace_772754
  have hstable : (prefixWord ++ tailWord_772754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772754).length < 2 ^ (prefixWord ++ tailWord_772754).sum := by decide
  have hdescent : baseEnd_772754 < baseStart_772754 := by decide
  rcases family_descends (prefixWord ++ tailWord_772754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772791 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 5]
def baseStart_772791 : Nat := 118140960795 + 772791 * 2 ^ 59
def prefixEnd_772791 : Nat := 4983230072969 + 3 ^ 40 * 772791 * 2
def baseEnd_772791 : Nat := 44090358718754576150945

theorem tailTrace_772791 : CollatzResearch.WordTrace tailWord_772791 prefixEnd_772791 44090358718754576150945 := by
  unfold tailWord_772791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28186003343317664040270227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18790668895545109360180151 28186003343317664040270227)
  ·
    refine ⟨42279005014976496060405341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28186003343317664040270227 42279005014976496060405341)
    ·
      refine ⟨15854626880616186022652003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42279005014976496060405341 15854626880616186022652003)
      ·
        refine ⟨23781940320924279033978005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15854626880616186022652003 23781940320924279033978005)
        ·
          refine ⟨1114778452543325579717719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23781940320924279033978005 1114778452543325579717719)
          ·
            refine ⟨1672167678814988369576579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114778452543325579717719 1672167678814988369576579)
            ·
              refine ⟨2508251518222482554364869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672167678814988369576579 2508251518222482554364869)
              ·
                refine ⟨470297159666715478943413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2508251518222482554364869 470297159666715478943413)
                ·
                  refine ⟨44090358718754576150945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470297159666715478943413 44090358718754576150945)
                  ·
                    rfl

theorem cell23_772791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 5].length) (baseStart_772791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772791 prefixEnd_772791 := by exact prefixLift 772791
  have htrace : WordTrace (prefixWord ++ tailWord_772791) baseStart_772791 baseEnd_772791 := by
    simpa [prefixWord, tailWord_772791, baseEnd_772791] using wordTrace_append hprefix tailTrace_772791
  have hstable : (prefixWord ++ tailWord_772791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772791).length < 2 ^ (prefixWord ++ tailWord_772791).sum := by decide
  have hdescent : baseEnd_772791 < baseStart_772791 := by decide
  rcases family_descends (prefixWord ++ tailWord_772791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772794 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2]
def baseStart_772794 : Nat := 118140960795 + 772794 * 2 ^ 59
def prefixEnd_772794 : Nat := 4983230072969 + 3 ^ 40 * 772794 * 2
def baseEnd_772794 : Nat := 396814768910754673620991

theorem tailTrace_772794 : CollatzResearch.WordTrace tailWord_772794 prefixEnd_772794 396814768910754673620991 := by
  unfold tailWord_772794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046528190576698888157359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18790741841537863701752957 7046528190576698888157359)
  ·
    refine ⟨10569792285865048332236039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046528190576698888157359 10569792285865048332236039)
    ·
      refine ⟨15854688428797572498354059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569792285865048332236039 15854688428797572498354059)
      ·
        refine ⟨23782032643196358747531089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15854688428797572498354059 23782032643196358747531089)
        ·
          refine ⟨17836524482397269060648317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23782032643196358747531089 17836524482397269060648317)
          ·
            refine ⟨6688696680898975897743119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17836524482397269060648317 6688696680898975897743119)
            ·
              refine ⟨10033045021348463846614679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688696680898975897743119 10033045021348463846614679)
              ·
                refine ⟨15049567532022695769922019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033045021348463846614679 15049567532022695769922019)
                ·
                  refine ⟨22574351298034043654883029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15049567532022695769922019 22574351298034043654883029)
                  ·
                    refine ⟨529086358547672898161321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22574351298034043654883029 529086358547672898161321)
                    ·
                      refine ⟨396814768910754673620991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529086358547672898161321 396814768910754673620991)
                      ·
                        rfl

theorem cell23_772794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2].length) (baseStart_772794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772794 prefixEnd_772794 := by exact prefixLift 772794
  have htrace : WordTrace (prefixWord ++ tailWord_772794) baseStart_772794 baseEnd_772794 := by
    simpa [prefixWord, tailWord_772794, baseEnd_772794] using wordTrace_append hprefix tailTrace_772794
  have hstable : (prefixWord ++ tailWord_772794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772794).length < 2 ^ (prefixWord ++ tailWord_772794).sum := by decide
  have hdescent : baseEnd_772794 < baseStart_772794 := by decide
  rcases family_descends (prefixWord ++ tailWord_772794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772821 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_772821 : Nat := 118140960795 + 772821 * 2 ^ 59
def prefixEnd_772821 : Nat := 4983230072969 + 3 ^ 40 * 772821 * 2
def baseEnd_772821 : Nat := 132276210962808689327789

theorem tailTrace_772821 : CollatzResearch.WordTrace tailWord_772821 prefixEnd_772821 132276210962808689327789 := by
  unfold tailWord_772821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28187097533208979163862317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18791398355472652775908211 28187097533208979163862317)
  ·
    refine ⟨10570161574953367186448369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28187097533208979163862317 10570161574953367186448369)
    ·
      refine ⟨7927621181215025389836277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10570161574953367186448369 7927621181215025389836277)
      ·
        refine ⟨743214485738908630297151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7927621181215025389836277 743214485738908630297151)
        ·
          refine ⟨1114821728608362945445727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743214485738908630297151 1114821728608362945445727)
          ·
            refine ⟨1672232592912544418168591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114821728608362945445727 1672232592912544418168591)
            ·
              refine ⟨2508348889368816627252887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672232592912544418168591 2508348889368816627252887)
              ·
                refine ⟨3762523334053224940879331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508348889368816627252887 3762523334053224940879331)
                ·
                  refine ⟨5643785001079837411318997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762523334053224940879331 5643785001079837411318997)
                  ·
                    refine ⟨132276210962808689327789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5643785001079837411318997 132276210962808689327789)
                    ·
                      rfl

theorem cell23_772821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_772821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772821 prefixEnd_772821 := by exact prefixLift 772821
  have htrace : WordTrace (prefixWord ++ tailWord_772821) baseStart_772821 baseEnd_772821 := by
    simpa [prefixWord, tailWord_772821, baseEnd_772821] using wordTrace_append hprefix tailTrace_772821
  have hstable : (prefixWord ++ tailWord_772821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772821).length < 2 ^ (prefixWord ++ tailWord_772821).sum := by decide
  have hdescent : baseEnd_772821 < baseStart_772821 := by decide
  rcases family_descends (prefixWord ++ tailWord_772821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772824 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_772824 : Nat := 118140960795 + 772824 * 2 ^ 59
def prefixEnd_772824 : Nat := 4983230072969 + 3 ^ 40 * 772824 * 2
def baseEnd_772824 : Nat := 396830173330389556245853

theorem tailTrace_772824 : CollatzResearch.WordTrace tailWord_772824 prefixEnd_772824 396830173330389556245853 := by
  unfold tailWord_772824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093603476099055338110763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18791471301465407117481017 14093603476099055338110763)
  ·
    refine ⟨21140405214148583007166145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14093603476099055338110763 21140405214148583007166145)
    ·
      refine ⟨15855303910611437255374609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21140405214148583007166145 15855303910611437255374609)
      ·
        refine ⟨11891477932958577941530957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15855303910611437255374609 11891477932958577941530957)
        ·
          refine ⟨4459304224859466728074109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11891477932958577941530957 4459304224859466728074109)
          ·
            refine ⟨1672239084322300023027791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4459304224859466728074109 1672239084322300023027791)
            ·
              refine ⟨2508358626483450034541687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672239084322300023027791 2508358626483450034541687)
              ·
                refine ⟨3762537939725175051812531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508358626483450034541687 3762537939725175051812531)
                ·
                  refine ⟨5643806909587762577718797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762537939725175051812531 5643806909587762577718797)
                  ·
                    refine ⟨2116427591095410966644549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5643806909587762577718797 2116427591095410966644549)
                    ·
                      refine ⟨396830173330389556245853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2116427591095410966644549 396830173330389556245853)
                      ·
                        rfl

theorem cell23_772824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_772824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772824 prefixEnd_772824 := by exact prefixLift 772824
  have htrace : WordTrace (prefixWord ++ tailWord_772824) baseStart_772824 baseEnd_772824 := by
    simpa [prefixWord, tailWord_772824, baseEnd_772824] using wordTrace_append hprefix tailTrace_772824
  have hstable : (prefixWord ++ tailWord_772824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772824).length < 2 ^ (prefixWord ++ tailWord_772824).sum := by decide
  have hdescent : baseEnd_772824 < baseStart_772824 := by decide
  rcases family_descends (prefixWord ++ tailWord_772824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772844 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 3]
def baseStart_772844 : Nat := 118140960795 + 772844 * 2 ^ 59
def prefixEnd_772844 : Nat := 4983230072969 + 3 ^ 40 * 772844 * 2
def baseEnd_772844 : Nat := 396840442943479477995761

theorem tailTrace_772844 : CollatzResearch.WordTrace tailWord_772844 prefixEnd_772844 396840442943479477995761 := by
  unfold tailWord_772844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093968206062827045974793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18791957608083769394633057 14093968206062827045974793)
  ·
    refine ⟨10570476154547120284481095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14093968206062827045974793 10570476154547120284481095)
    ·
      refine ⟨15855714231820680426721643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570476154547120284481095 15855714231820680426721643)
      ·
        refine ⟨23783571347731020640082465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15855714231820680426721643 23783571347731020640082465)
        ·
          refine ⟨17837678510798265480061849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23783571347731020640082465 17837678510798265480061849)
          ·
            refine ⟨13378258883098699110046387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17837678510798265480061849 13378258883098699110046387)
            ·
              refine ⟨20067388324648048665069581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378258883098699110046387 20067388324648048665069581)
              ·
                refine ⟨7525270621743018249401093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20067388324648048665069581 7525270621743018249401093)
                ·
                  refine ⟨1410988241576815921762705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7525270621743018249401093 1410988241576815921762705)
                  ·
                    refine ⟨1058241181182611941322029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1410988241576815921762705 1058241181182611941322029)
                    ·
                      refine ⟨396840442943479477995761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058241181182611941322029 396840442943479477995761)
                      ·
                        rfl

theorem cell23_772844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_772844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772844 prefixEnd_772844 := by exact prefixLift 772844
  have htrace : WordTrace (prefixWord ++ tailWord_772844) baseStart_772844 baseEnd_772844 := by
    simpa [prefixWord, tailWord_772844, baseEnd_772844] using wordTrace_append hprefix tailTrace_772844
  have hstable : (prefixWord ++ tailWord_772844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772844).length < 2 ^ (prefixWord ++ tailWord_772844).sum := by decide
  have hdescent : baseEnd_772844 < baseStart_772844 := by decide
  rcases family_descends (prefixWord ++ tailWord_772844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772854 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6]
def baseStart_772854 : Nat := 118140960795 + 772854 * 2 ^ 59
def prefixEnd_772854 : Nat := 4983230072969 + 3 ^ 40 * 772854 * 2
def baseEnd_772854 : Nat := 396845577750024438870715

theorem tailTrace_772854 : CollatzResearch.WordTrace tailWord_772854 prefixEnd_772854 396845577750024438870715 := by
  unfold tailWord_772854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761768821380589112488351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18792200761392950533209077 1761768821380589112488351)
  ·
    refine ⟨2642653232070883668732527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1761768821380589112488351 2642653232070883668732527)
    ·
      refine ⟨3963979848106325503098791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642653232070883668732527 3963979848106325503098791)
      ·
        refine ⟨5945969772159488254648187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963979848106325503098791 5945969772159488254648187)
        ·
          refine ⟨8918954658239232381972281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945969772159488254648187 8918954658239232381972281)
          ·
            refine ⟨6689215993679424286479211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918954658239232381972281 6689215993679424286479211)
            ·
              refine ⟨10033823990519136429718817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689215993679424286479211 10033823990519136429718817)
              ·
                refine ⟨7525367992889352322289113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10033823990519136429718817 7525367992889352322289113)
                ·
                  refine ⟨5644025994667014241716835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525367992889352322289113 5644025994667014241716835)
                  ·
                    refine ⟨8466038992000521362575253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644025994667014241716835 8466038992000521362575253)
                    ·
                      refine ⟨396845577750024438870715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8466038992000521362575253 396845577750024438870715)
                      ·
                        rfl

theorem cell23_772854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_772854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772854 prefixEnd_772854 := by exact prefixLift 772854
  have htrace : WordTrace (prefixWord ++ tailWord_772854) baseStart_772854 baseEnd_772854 := by
    simpa [prefixWord, tailWord_772854, baseEnd_772854] using wordTrace_append hprefix tailTrace_772854
  have hstable : (prefixWord ++ tailWord_772854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772854).length < 2 ^ (prefixWord ++ tailWord_772854).sum := by decide
  have hdescent : baseEnd_772854 < baseStart_772854 := by decide
  rcases family_descends (prefixWord ++ tailWord_772854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_772867 : Nat := 118140960795 + 772867 * 2 ^ 59
def prefixEnd_772867 : Nat := 4983230072969 + 3 ^ 40 * 772867 * 2
def baseEnd_772867 : Nat := 396852252998532888008155

theorem tailTrace_772867 : CollatzResearch.WordTrace tailWord_772867 prefixEnd_772867 396852252998532888008155 := by
  unfold tailWord_772867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28188775291042329020036855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18792516860694886013357903 28188775291042329020036855)
  ·
    refine ⟨42283162936563493530055283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28188775291042329020036855 42283162936563493530055283)
    ·
      refine ⟨63424744404845240295082925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42283162936563493530055283 63424744404845240295082925)
      ·
        refine ⟨23784279151816965110656097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63424744404845240295082925 23784279151816965110656097)
        ·
          refine ⟨17838209363862723832992073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23784279151816965110656097 17838209363862723832992073)
          ·
            refine ⟨13378657022897042874744055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17838209363862723832992073 13378657022897042874744055)
            ·
              refine ⟨20067985534345564312116083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378657022897042874744055 20067985534345564312116083)
              ·
                refine ⟨30101978301518346468174125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20067985534345564312116083 30101978301518346468174125)
                ·
                  refine ⟨11288241863069379925565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30101978301518346468174125 11288241863069379925565297)
                  ·
                    refine ⟨8466181397302034944173973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11288241863069379925565297 8466181397302034944173973)
                    ·
                      refine ⟨396852252998532888008155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8466181397302034944173973 396852252998532888008155)
                      ·
                        rfl

theorem cell23_772867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_772867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772867 prefixEnd_772867 := by exact prefixLift 772867
  have htrace : WordTrace (prefixWord ++ tailWord_772867) baseStart_772867 baseEnd_772867 := by
    simpa [prefixWord, tailWord_772867, baseEnd_772867] using wordTrace_append hprefix tailTrace_772867
  have hstable : (prefixWord ++ tailWord_772867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772867).length < 2 ^ (prefixWord ++ tailWord_772867).sum := by decide
  have hdescent : baseEnd_772867 < baseStart_772867 := by decide
  rcases family_descends (prefixWord ++ tailWord_772867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772874 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_772874 : Nat := 118140960795 + 772874 * 2 ^ 59
def prefixEnd_772874 : Nat := 4983230072969 + 3 ^ 40 * 772874 * 2
def baseEnd_772874 : Nat := 396855847363114360620623

theorem tailTrace_772874 : CollatzResearch.WordTrace tailWord_772874 prefixEnd_772874 396855847363114360620623 := by
  unfold tailWord_772874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047257650504242303885419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18792687068011312810361117 7047257650504242303885419)
  ·
    refine ⟨10570886475756363455828129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047257650504242303885419 10570886475756363455828129)
    ·
      refine ⟨7928164856817272591871097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10570886475756363455828129 7928164856817272591871097)
      ·
        refine ⟨5946123642612954443903323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7928164856817272591871097 5946123642612954443903323)
        ·
          refine ⟨8919185463919431665854985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946123642612954443903323 8919185463919431665854985)
          ·
            refine ⟨6689389097939573749391239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919185463919431665854985 6689389097939573749391239)
            ·
              refine ⟨10034083646909360624086859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689389097939573749391239 10034083646909360624086859)
              ·
                refine ⟨15051125470364040936130289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034083646909360624086859 15051125470364040936130289)
                ·
                  refine ⟨11288344102773030702097717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15051125470364040936130289 11288344102773030702097717)
                  ·
                    refine ⟨1058282259634971628321661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11288344102773030702097717 1058282259634971628321661)
                    ·
                      refine ⟨396855847363114360620623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058282259634971628321661 396855847363114360620623)
                      ·
                        rfl

theorem cell23_772874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_772874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772874 prefixEnd_772874 := by exact prefixLift 772874
  have htrace : WordTrace (prefixWord ++ tailWord_772874) baseStart_772874 baseEnd_772874 := by
    simpa [prefixWord, tailWord_772874, baseEnd_772874] using wordTrace_append hprefix tailTrace_772874
  have hstable : (prefixWord ++ tailWord_772874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772874).length < 2 ^ (prefixWord ++ tailWord_772874).sum := by decide
  have hdescent : baseEnd_772874 < baseStart_772874 := by decide
  rcases family_descends (prefixWord ++ tailWord_772874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772924 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_772924 : Nat := 118140960795 + 772924 * 2 ^ 59
def prefixEnd_772924 : Nat := 4983230072969 + 3 ^ 40 * 772924 * 2
def baseEnd_772924 : Nat := 132293840465279721665131

theorem tailTrace_772924 : CollatzResearch.WordTrace tailWord_772924 prefixEnd_772924 132293840465279721665131 := by
  unfold tailWord_772924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095427125917913877430913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18793902834557218503241217 14095427125917913877430913)
  ·
    refine ⟨10571570344438435408073185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14095427125917913877430913 10571570344438435408073185)
    ·
      refine ⟨7928677758328826556054889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10571570344438435408073185 7928677758328826556054889)
      ·
        refine ⟨5946508318746619917041167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7928677758328826556054889 5946508318746619917041167)
        ·
          refine ⟨8919762478119929875561751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946508318746619917041167 8919762478119929875561751)
          ·
            refine ⟨13379643717179894813342627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8919762478119929875561751 13379643717179894813342627)
            ·
              refine ⟨20069465575769842220013941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13379643717179894813342627 20069465575769842220013941)
              ·
                refine ⟨1881512397728422708126307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20069465575769842220013941 1881512397728422708126307)
                ·
                  refine ⟨2822268596592634062189461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881512397728422708126307 2822268596592634062189461)
                  ·
                    refine ⟨132293840465279721665131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2822268596592634062189461 132293840465279721665131)
                    ·
                      rfl

theorem cell23_772924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_772924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772924 prefixEnd_772924 := by exact prefixLift 772924
  have htrace : WordTrace (prefixWord ++ tailWord_772924) baseStart_772924 baseEnd_772924 := by
    simpa [prefixWord, tailWord_772924, baseEnd_772924] using wordTrace_append hprefix tailTrace_772924
  have hstable : (prefixWord ++ tailWord_772924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772924).length < 2 ^ (prefixWord ++ tailWord_772924).sum := by decide
  have hdescent : baseEnd_772924 < baseStart_772924 := by decide
  rcases family_descends (prefixWord ++ tailWord_772924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772944 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_772944 : Nat := 118140960795 + 772944 * 2 ^ 59
def prefixEnd_772944 : Nat := 4983230072969 + 3 ^ 40 * 772944 * 2
def baseEnd_772944 : Nat := 396891791008929086745301

theorem tailTrace_772944 : CollatzResearch.WordTrace tailWord_772944 prefixEnd_772944 396891791008929086745301 := by
  unfold tailWord_772944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095791855881685585294943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18794389141175580780393257 14095791855881685585294943)
  ·
    refine ⟨21143687783822528377942415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14095791855881685585294943 21143687783822528377942415)
    ·
      refine ⟨31715531675733792566913623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21143687783822528377942415 31715531675733792566913623)
      ·
        refine ⟨47573297513600688850370435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31715531675733792566913623 47573297513600688850370435)
        ·
          refine ⟨71359946270401033275555653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47573297513600688850370435 71359946270401033275555653)
          ·
            refine ⟨13379989925700193739166685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71359946270401033275555653 13379989925700193739166685)
            ·
              refine ⟨5017496222137572652187507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13379989925700193739166685 5017496222137572652187507)
              ·
                refine ⟨7526244333206358978281261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017496222137572652187507 7526244333206358978281261)
                ·
                  refine ⟨2822341624952384616855473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7526244333206358978281261 2822341624952384616855473)
                  ·
                    refine ⟨2116756218714288462641605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2822341624952384616855473 2116756218714288462641605)
                    ·
                      refine ⟨396891791008929086745301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2116756218714288462641605 396891791008929086745301)
                      ·
                        rfl

theorem cell23_772944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_772944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772944 prefixEnd_772944 := by exact prefixLift 772944
  have htrace : WordTrace (prefixWord ++ tailWord_772944) baseStart_772944 baseEnd_772944 := by
    simpa [prefixWord, tailWord_772944, baseEnd_772944] using wordTrace_append hprefix tailTrace_772944
  have hstable : (prefixWord ++ tailWord_772944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772944).length < 2 ^ (prefixWord ++ tailWord_772944).sum := by decide
  have hdescent : baseEnd_772944 < baseStart_772944 := by decide
  rcases family_descends (prefixWord ++ tailWord_772944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772951 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_772951 : Nat := 118140960795 + 772951 * 2 ^ 59
def prefixEnd_772951 : Nat := 4983230072969 + 3 ^ 40 * 772951 * 2
def baseEnd_772951 : Nat := 396895385373510559357769

theorem tailTrace_772951 : CollatzResearch.WordTrace tailWord_772951 prefixEnd_772951 396895385373510559357769 := by
  unfold tailWord_772951
  simp only [CollatzResearch.WordTrace]
  refine ⟨28191839022738011366094707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18794559348492007577396471 28191839022738011366094707)
  ·
    refine ⟨42287758534107017049142061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28191839022738011366094707 42287758534107017049142061)
    ·
      refine ⟨15857909450290131393428273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42287758534107017049142061 15857909450290131393428273)
      ·
        refine ⟨11893432087717598545071205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15857909450290131393428273 11893432087717598545071205)
        ·
          refine ⟨2230018516447049727200851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11893432087717598545071205 2230018516447049727200851)
          ·
            refine ⟨3345027774670574590801277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230018516447049727200851 3345027774670574590801277)
            ·
              refine ⟨1254385415501465471550479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3345027774670574590801277 1254385415501465471550479)
              ·
                refine ⟨1881578123252198207325719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254385415501465471550479 1881578123252198207325719)
                ·
                  refine ⟨2822367184878297310988579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881578123252198207325719 2822367184878297310988579)
                  ·
                    refine ⟨4233550777317445966482869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2822367184878297310988579 4233550777317445966482869)
                    ·
                      refine ⟨396895385373510559357769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4233550777317445966482869 396895385373510559357769)
                      ·
                        rfl

theorem cell23_772951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_772951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772951 prefixEnd_772951 := by exact prefixLift 772951
  have htrace : WordTrace (prefixWord ++ tailWord_772951) baseStart_772951 baseEnd_772951 := by
    simpa [prefixWord, tailWord_772951, baseEnd_772951] using wordTrace_append hprefix tailTrace_772951
  have hstable : (prefixWord ++ tailWord_772951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772951).length < 2 ^ (prefixWord ++ tailWord_772951).sum := by decide
  have hdescent : baseEnd_772951 < baseStart_772951 := by decide
  rcases family_descends (prefixWord ++ tailWord_772951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_772982 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2]
def baseStart_772982 : Nat := 118140960795 + 772982 * 2 ^ 59
def prefixEnd_772982 : Nat := 4983230072969 + 3 ^ 40 * 772982 * 2
def baseEnd_772982 : Nat := 396911303273799938070127

theorem tailTrace_772982 : CollatzResearch.WordTrace tailWord_772982 prefixEnd_772982 396911303273799938070127 := by
  unfold tailWord_772982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762060605351606478779575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18795313123750469106982133 1762060605351606478779575)
  ·
    refine ⟨2643090908027409718169363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1762060605351606478779575 2643090908027409718169363)
    ·
      refine ⟨3964636362041114577254045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643090908027409718169363 3964636362041114577254045)
      ·
        refine ⟨1486738635765417966470267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3964636362041114577254045 1486738635765417966470267)
        ·
          refine ⟨2230107953648126949705401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486738635765417966470267 2230107953648126949705401)
          ·
            refine ⟨1672580965236095212279051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230107953648126949705401 1672580965236095212279051)
            ·
              refine ⟨2508871447854142818418577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672580965236095212279051 2508871447854142818418577)
              ·
                refine ⟨1881653585890607113813933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508871447854142818418577 1881653585890607113813933)
                ·
                  refine ⟨705620094708977667680225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1881653585890607113813933 705620094708977667680225)
                  ·
                    refine ⟨529215071031733250760169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705620094708977667680225 529215071031733250760169)
                    ·
                      refine ⟨396911303273799938070127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529215071031733250760169 396911303273799938070127)
                      ·
                        rfl

theorem cell23_772982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_772982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_772982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_772982 prefixEnd_772982 := by exact prefixLift 772982
  have htrace : WordTrace (prefixWord ++ tailWord_772982) baseStart_772982 baseEnd_772982 := by
    simpa [prefixWord, tailWord_772982, baseEnd_772982] using wordTrace_append hprefix tailTrace_772982
  have hstable : (prefixWord ++ tailWord_772982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_772982).length < 2 ^ (prefixWord ++ tailWord_772982).sum := by decide
  have hdescent : baseEnd_772982 < baseStart_772982 := by decide
  rcases family_descends (prefixWord ++ tailWord_772982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773002 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3]
def baseStart_773002 : Nat := 118140960795 + 773002 * 2 ^ 59
def prefixEnd_773002 : Nat := 4983230072969 + 3 ^ 40 * 773002 * 2
def baseEnd_773002 : Nat := 396921572886889859820035

theorem tailTrace_773002 : CollatzResearch.WordTrace tailWord_773002 prefixEnd_773002 396921572886889859820035 := by
  unfold tailWord_773002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7048424786388311769050315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18795799430368831384134173 7048424786388311769050315)
  ·
    refine ⟨10572637179582467653575473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7048424786388311769050315 10572637179582467653575473)
    ·
      refine ⟨7929477884686850740181605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10572637179582467653575473 7929477884686850740181605)
      ·
        refine ⟨1486777103378784513784051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7929477884686850740181605 1486777103378784513784051)
        ·
          refine ⟨2230165655068176770676077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486777103378784513784051 2230165655068176770676077)
          ·
            refine ⟨836312120650566289003529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2230165655068176770676077 836312120650566289003529)
            ·
              refine ⟨627234090487924716752647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836312120650566289003529 627234090487924716752647)
              ·
                refine ⟨940851135731887075128971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627234090487924716752647 940851135731887075128971)
                ·
                  refine ⟨1411276703597830612693457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940851135731887075128971 1411276703597830612693457)
                  ·
                    refine ⟨1058457527698372959520093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1411276703597830612693457 1058457527698372959520093)
                    ·
                      refine ⟨396921572886889859820035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058457527698372959520093 396921572886889859820035)
                      ·
                        rfl

theorem cell23_773002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_773002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773002 prefixEnd_773002 := by exact prefixLift 773002
  have htrace : WordTrace (prefixWord ++ tailWord_773002) baseStart_773002 baseEnd_773002 := by
    simpa [prefixWord, tailWord_773002, baseEnd_773002] using wordTrace_append hprefix tailTrace_773002
  have hstable : (prefixWord ++ tailWord_773002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773002).length < 2 ^ (prefixWord ++ tailWord_773002).sum := by decide
  have hdescent : baseEnd_773002 < baseStart_773002 := by decide
  rcases family_descends (prefixWord ++ tailWord_773002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773091 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 4, 5]
def baseStart_773091 : Nat := 118140960795 + 773091 * 2 ^ 59
def prefixEnd_773091 : Nat := 4983230072969 + 3 ^ 40 * 773091 * 2
def baseEnd_773091 : Nat := 132322424221713337202375

theorem tailTrace_773091 : CollatzResearch.WordTrace tailWord_773091 prefixEnd_773091 132322424221713337202375 := by
  unfold tailWord_773091
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196945242230815276191127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18797963494820543517460751 28196945242230815276191127)
  ·
    refine ⟨42295417863346222914286691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28196945242230815276191127 42295417863346222914286691)
    ·
      refine ⟨63443126795019334371430037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42295417863346222914286691 63443126795019334371430037)
      ·
        refine ⟨2973896568516531298660783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63443126795019334371430037 2973896568516531298660783)
        ·
          refine ⟨4460844852774796947991175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973896568516531298660783 4460844852774796947991175)
          ·
            refine ⟨6691267279162195421986763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460844852774796947991175 6691267279162195421986763)
            ·
              refine ⟨10036900918743293132980145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691267279162195421986763 10036900918743293132980145)
              ·
                refine ⟨7527675689057469849735109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036900918743293132980145 7527675689057469849735109)
                ·
                  refine ⟨1411439191698275596825333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7527675689057469849735109 1411439191698275596825333)
                  ·
                    refine ⟨132322424221713337202375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1411439191698275596825333 132322424221713337202375)
                    ·
                      rfl

theorem cell23_773091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].length) (baseStart_773091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773091 prefixEnd_773091 := by exact prefixLift 773091
  have htrace : WordTrace (prefixWord ++ tailWord_773091) baseStart_773091 baseEnd_773091 := by
    simpa [prefixWord, tailWord_773091, baseEnd_773091] using wordTrace_append hprefix tailTrace_773091
  have hstable : (prefixWord ++ tailWord_773091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773091).length < 2 ^ (prefixWord ++ tailWord_773091).sum := by decide
  have hdescent : baseEnd_773091 < baseStart_773091 := by decide
  rcases family_descends (prefixWord ++ tailWord_773091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773128 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_773128 : Nat := 118140960795 + 773128 * 2 ^ 59
def prefixEnd_773128 : Nat := 4983230072969 + 3 ^ 40 * 773128 * 2
def baseEnd_773128 : Nat := 396986271449356366844455

theorem tailTrace_773128 : CollatzResearch.WordTrace tailWord_773128 prefixEnd_773128 396986271449356366844455 := by
  unfold tailWord_773128
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099147371548385297644019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18798863162064513730192025 14099147371548385297644019)
  ·
    refine ⟨21148721057322577946466029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14099147371548385297644019 21148721057322577946466029)
    ·
      refine ⟨7930770396495966729924761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21148721057322577946466029 7930770396495966729924761)
      ·
        refine ⟨5948077797371975047443571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7930770396495966729924761 5948077797371975047443571)
        ·
          refine ⟨8922116696057962571165357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948077797371975047443571 8922116696057962571165357)
          ·
            refine ⟨3345793761021735964187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8922116696057962571165357 3345793761021735964187009)
            ·
              refine ⟨2509345320766301973140257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3345793761021735964187009 2509345320766301973140257)
              ·
                refine ⟨1882008990574726479855193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509345320766301973140257 1882008990574726479855193)
                ·
                  refine ⟨1411506742931044859891395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882008990574726479855193 1411506742931044859891395)
                  ·
                    refine ⟨2117260114396567289837093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411506742931044859891395 2117260114396567289837093)
                    ·
                      refine ⟨396986271449356366844455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2117260114396567289837093 396986271449356366844455)
                      ·
                        rfl

theorem cell23_773128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_773128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773128 prefixEnd_773128 := by exact prefixLift 773128
  have htrace : WordTrace (prefixWord ++ tailWord_773128) baseStart_773128 baseEnd_773128 := by
    simpa [prefixWord, tailWord_773128, baseEnd_773128] using wordTrace_append hprefix tailTrace_773128
  have hstable : (prefixWord ++ tailWord_773128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773128).length < 2 ^ (prefixWord ++ tailWord_773128).sum := by decide
  have hdescent : baseEnd_773128 < baseStart_773128 := by decide
  rcases family_descends (prefixWord ++ tailWord_773128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773162 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_773162 : Nat := 118140960795 + 773162 * 2 ^ 59
def prefixEnd_773162 : Nat := 4983230072969 + 3 ^ 40 * 773162 * 2
def baseEnd_773162 : Nat := 397003729791609233819299

theorem tailTrace_773162 : CollatzResearch.WordTrace tailWord_773162 prefixEnd_773162 397003729791609233819299 := by
  unfold tailWord_773162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049883706243398600506435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18799689883315729601350493 7049883706243398600506435)
  ·
    refine ⟨10574825559365097900759653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7049883706243398600506435 10574825559365097900759653)
    ·
      refine ⟨1982779792380955856392435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10574825559365097900759653 1982779792380955856392435)
      ·
        refine ⟨2974169688571433784588653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982779792380955856392435 2974169688571433784588653)
        ·
          refine ⟨1115313633214287669220745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2974169688571433784588653 1115313633214287669220745)
          ·
            refine ⟨836485224910715751915559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115313633214287669220745 836485224910715751915559)
            ·
              refine ⟨1254727837366073627873339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836485224910715751915559 1254727837366073627873339)
              ·
                refine ⟨1882091756049110441810009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254727837366073627873339 1882091756049110441810009)
                ·
                  refine ⟨1411568817036832831357507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882091756049110441810009 1411568817036832831357507)
                  ·
                    refine ⟨2117353225555249247036261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1411568817036832831357507 2117353225555249247036261)
                    ·
                      refine ⟨397003729791609233819299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2117353225555249247036261 397003729791609233819299)
                      ·
                        rfl

theorem cell23_773162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_773162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773162 prefixEnd_773162 := by exact prefixLift 773162
  have htrace : WordTrace (prefixWord ++ tailWord_773162) baseStart_773162 baseEnd_773162 := by
    simpa [prefixWord, tailWord_773162, baseEnd_773162] using wordTrace_append hprefix tailTrace_773162
  have hstable : (prefixWord ++ tailWord_773162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773162).length < 2 ^ (prefixWord ++ tailWord_773162).sum := by decide
  have hdescent : baseEnd_773162 < baseStart_773162 := by decide
  rcases family_descends (prefixWord ++ tailWord_773162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773228 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_773228 : Nat := 118140960795 + 773228 * 2 ^ 59
def prefixEnd_773228 : Nat := 4983230072969 + 3 ^ 40 * 773228 * 2
def baseEnd_773228 : Nat := 132345873171601991864665

theorem tailTrace_773228 : CollatzResearch.WordTrace tailWord_773228 prefixEnd_773228 132345873171601991864665 := by
  unfold tailWord_773228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100971021367243836964169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18801294695156325115952225 14100971021367243836964169)
  ·
    refine ⟨10575728266025432877723127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14100971021367243836964169 10575728266025432877723127)
    ·
      refine ⟨15863592399038149316584691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10575728266025432877723127 15863592399038149316584691)
      ·
        refine ⟨23795388598557223974877037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863592399038149316584691 23795388598557223974877037)
        ·
          refine ⟨8923270724458958990578889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23795388598557223974877037 8923270724458958990578889)
          ·
            refine ⟨6692453043344219242934167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923270724458958990578889 6692453043344219242934167)
            ·
              refine ⟨10038679565016328864401251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692453043344219242934167 10038679565016328864401251)
              ·
                refine ⟨15058019347524493296601877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10038679565016328864401251 15058019347524493296601877)
                ·
                  refine ⟨705844656915210623278213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15058019347524493296601877 705844656915210623278213)
                  ·
                    refine ⟨132345873171601991864665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705844656915210623278213 132345873171601991864665)
                    ·
                      rfl

theorem cell23_773228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_773228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773228 prefixEnd_773228 := by exact prefixLift 773228
  have htrace : WordTrace (prefixWord ++ tailWord_773228) baseStart_773228 baseEnd_773228 := by
    simpa [prefixWord, tailWord_773228, baseEnd_773228] using wordTrace_append hprefix tailTrace_773228
  have hstable : (prefixWord ++ tailWord_773228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773228).length < 2 ^ (prefixWord ++ tailWord_773228).sum := by decide
  have hdescent : baseEnd_773228 < baseStart_773228 := by decide
  rcases family_descends (prefixWord ++ tailWord_773228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773229 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_773229 : Nat := 118140960795 + 773229 * 2 ^ 59
def prefixEnd_773229 : Nat := 4983230072969 + 3 ^ 40 * 773229 * 2
def baseEnd_773229 : Nat := 397038132995460471681491

theorem tailTrace_773229 : CollatzResearch.WordTrace tailWord_773229 prefixEnd_773229 397038132995460471681491 := by
  unfold tailWord_773229
  simp only [CollatzResearch.WordTrace]
  refine ⟨28201978515730864844714741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18801319010487243229809827 28201978515730864844714741)
  ·
    refine ⟨2643935485849768579192007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28201978515730864844714741 2643935485849768579192007)
    ·
      refine ⟨3965903228774652868788011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643935485849768579192007 3965903228774652868788011)
      ·
        refine ⟨5948854843161979303182017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965903228774652868788011 5948854843161979303182017)
        ·
          refine ⟨4461641132371484477386513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5948854843161979303182017 4461641132371484477386513)
          ·
            refine ⟨3346230849278613358039885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4461641132371484477386513 3346230849278613358039885)
            ·
              refine ⟨1254836568479480009264957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3346230849278613358039885 1254836568479480009264957)
              ·
                refine ⟨470563713179805003474359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254836568479480009264957 470563713179805003474359)
                ·
                  refine ⟨705845569769707505211539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470563713179805003474359 705845569769707505211539)
                  ·
                    refine ⟨1058768354654561257817309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 705845569769707505211539 1058768354654561257817309)
                    ·
                      refine ⟨397038132995460471681491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058768354654561257817309 397038132995460471681491)
                      ·
                        rfl

theorem cell23_773229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_773229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773229 prefixEnd_773229 := by exact prefixLift 773229
  have htrace : WordTrace (prefixWord ++ tailWord_773229) baseStart_773229 baseEnd_773229 := by
    simpa [prefixWord, tailWord_773229, baseEnd_773229] using wordTrace_append hprefix tailTrace_773229
  have hstable : (prefixWord ++ tailWord_773229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773229).length < 2 ^ (prefixWord ++ tailWord_773229).sum := by decide
  have hdescent : baseEnd_773229 < baseStart_773229 := by decide
  rcases family_descends (prefixWord ++ tailWord_773229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773245 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_773245 : Nat := 118140960795 + 773245 * 2 ^ 59
def prefixEnd_773245 : Nat := 4983230072969 + 3 ^ 40 * 773245 * 2
def baseEnd_773245 : Nat := 132348782895310803027139

theorem tailTrace_773245 : CollatzResearch.WordTrace tailWord_773245 prefixEnd_773245 132348782895310803027139 := by
  unfold tailWord_773245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202562083672899577297189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18801708055781933051531459 28202562083672899577297189)
  ·
    refine ⟨5287980390688668670743223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28202562083672899577297189 5287980390688668670743223)
    ·
      refine ⟨7931970586033003006114835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287980390688668670743223 7931970586033003006114835)
      ·
        refine ⟨11897955879049504509172253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7931970586033003006114835 11897955879049504509172253)
        ·
          refine ⟨4461733454643564190939595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11897955879049504509172253 4461733454643564190939595)
          ·
            refine ⟨6692600181965346286409393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461733454643564190939595 6692600181965346286409393)
            ·
              refine ⟨5019450136474009714807045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6692600181965346286409393 5019450136474009714807045)
              ·
                refine ⟨941146900588876821526321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5019450136474009714807045 941146900588876821526321)
                ·
                  refine ⟨705860175441657616144741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941146900588876821526321 705860175441657616144741)
                  ·
                    refine ⟨132348782895310803027139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705860175441657616144741 132348782895310803027139)
                    ·
                      rfl

theorem cell23_773245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_773245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773245 prefixEnd_773245 := by exact prefixLift 773245
  have htrace : WordTrace (prefixWord ++ tailWord_773245) baseStart_773245 baseEnd_773245 := by
    simpa [prefixWord, tailWord_773245, baseEnd_773245] using wordTrace_append hprefix tailTrace_773245
  have hstable : (prefixWord ++ tailWord_773245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773245).length < 2 ^ (prefixWord ++ tailWord_773245).sum := by decide
  have hdescent : baseEnd_773245 < baseStart_773245 := by decide
  rcases family_descends (prefixWord ++ tailWord_773245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773258 : List Nat := [3, 1, 2, 3, 1, 1, 4, 8]
def baseStart_773258 : Nat := 118140960795 + 773258 * 2 ^ 59
def prefixEnd_773258 : Nat := 4983230072969 + 3 ^ 40 * 773258 * 2
def baseEnd_773258 : Nat := 14705667553127439193291

theorem tailTrace_773258 : CollatzResearch.WordTrace tailWord_773258 prefixEnd_773258 14705667553127439193291 := by
  unfold tailWord_773258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050759058156450699380107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18802024155083868531680285 7050759058156450699380107)
  ·
    refine ⟨10576138587234676049070161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7050759058156450699380107 10576138587234676049070161)
    ·
      refine ⟨7932103940426007036802621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10576138587234676049070161 7932103940426007036802621)
      ·
        refine ⟨2974538977659752638800983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932103940426007036802621 2974538977659752638800983)
        ·
          refine ⟨4461808466489628958201475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974538977659752638800983 4461808466489628958201475)
          ·
            refine ⟨6692712699734443437302213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461808466489628958201475 6692712699734443437302213)
            ·
              refine ⟨1254883631200208144494165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6692712699734443437302213 1254883631200208144494165)
              ·
                refine ⟨14705667553127439193291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1254883631200208144494165 14705667553127439193291)
                ·
                  rfl

theorem cell23_773258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_773258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773258 prefixEnd_773258 := by exact prefixLift 773258
  have htrace : WordTrace (prefixWord ++ tailWord_773258) baseStart_773258 baseEnd_773258 := by
    simpa [prefixWord, tailWord_773258, baseEnd_773258] using wordTrace_append hprefix tailTrace_773258
  have hstable : (prefixWord ++ tailWord_773258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773258).length < 2 ^ (prefixWord ++ tailWord_773258).sum := by decide
  have hdescent : baseEnd_773258 < baseStart_773258 := by decide
  rcases family_descends (prefixWord ++ tailWord_773258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773262 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 2, 4]
def baseStart_773262 : Nat := 118140960795 + 773262 * 2 ^ 59
def prefixEnd_773262 : Nat := 4983230072969 + 3 ^ 40 * 773262 * 2
def baseEnd_773262 : Nat := 132351692619019614189613

theorem tailTrace_773262 : CollatzResearch.WordTrace tailWord_773262 prefixEnd_773262 132351692619019614189613 := by
  unfold tailWord_773262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525397765576413935083255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18802121416407540987110693 3525397765576413935083255)
  ·
    refine ⟨5288096648364620902624883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525397765576413935083255 5288096648364620902624883)
    ·
      refine ⟨7932144972546931353937325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288096648364620902624883 7932144972546931353937325)
      ·
        refine ⟨2974554364705099257726497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932144972546931353937325 2974554364705099257726497)
        ·
          refine ⟨2230915773528824443294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974554364705099257726497 2230915773528824443294873)
          ·
            refine ⟨1673186830146618332471155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230915773528824443294873 1673186830146618332471155)
            ·
              refine ⟨2509780245219927498706733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673186830146618332471155 2509780245219927498706733)
              ·
                refine ⟨941167591957472812015025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2509780245219927498706733 941167591957472812015025)
                ·
                  refine ⟨705875693968104609011269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941167591957472812015025 705875693968104609011269)
                  ·
                    refine ⟨132351692619019614189613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 705875693968104609011269 132351692619019614189613)
                    ·
                      rfl

theorem cell23_773262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_773262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773262 prefixEnd_773262 := by exact prefixLift 773262
  have htrace : WordTrace (prefixWord ++ tailWord_773262) baseStart_773262 baseEnd_773262 := by
    simpa [prefixWord, tailWord_773262, baseEnd_773262] using wordTrace_append hprefix tailTrace_773262
  have hstable : (prefixWord ++ tailWord_773262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773262).length < 2 ^ (prefixWord ++ tailWord_773262).sum := by decide
  have hdescent : baseEnd_773262 < baseStart_773262 := by decide
  rcases family_descends (prefixWord ++ tailWord_773262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773272 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_773272 : Nat := 118140960795 + 773272 * 2 ^ 59
def prefixEnd_773272 : Nat := 4983230072969 + 3 ^ 40 * 773272 * 2
def baseEnd_773272 : Nat := 397060212663603803443793

theorem tailTrace_773272 : CollatzResearch.WordTrace tailWord_773272 prefixEnd_773272 397060212663603803443793 := by
  unfold tailWord_773272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101773427287541594265035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18802364569716722125686713 14101773427287541594265035)
  ·
    refine ⟨21152660140931312391397553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14101773427287541594265035 21152660140931312391397553)
    ·
      refine ⟨15864495105698484293548165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21152660140931312391397553 15864495105698484293548165)
      ·
        refine ⟨2974592832318465805040281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15864495105698484293548165 2974592832318465805040281)
        ·
          refine ⟨2230944624238849353780211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974592832318465805040281 2230944624238849353780211)
          ·
            refine ⟨3346416936358274030670317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230944624238849353780211 3346416936358274030670317)
            ·
              refine ⟨1254906351134352761501369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3346416936358274030670317 1254906351134352761501369)
              ·
                refine ⟨941179763350764571126027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1254906351134352761501369 941179763350764571126027)
                ·
                  refine ⟨1411769645026146856689041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941179763350764571126027 1411769645026146856689041)
                  ·
                    refine ⟨1058827233769610142516781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1411769645026146856689041 1058827233769610142516781)
                    ·
                      refine ⟨397060212663603803443793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058827233769610142516781 397060212663603803443793)
                      ·
                        rfl

theorem cell23_773272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_773272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773272 prefixEnd_773272 := by exact prefixLift 773272
  have htrace : WordTrace (prefixWord ++ tailWord_773272) baseStart_773272 baseEnd_773272 := by
    simpa [prefixWord, tailWord_773272, baseEnd_773272] using wordTrace_append hprefix tailTrace_773272
  have hstable : (prefixWord ++ tailWord_773272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773272).length < 2 ^ (prefixWord ++ tailWord_773272).sum := by decide
  have hdescent : baseEnd_773272 < baseStart_773272 := by decide
  rcases family_descends (prefixWord ++ tailWord_773272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773282 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_773282 : Nat := 118140960795 + 773282 * 2 ^ 59
def prefixEnd_773282 : Nat := 4983230072969 + 3 ^ 40 * 773282 * 2
def baseEnd_773282 : Nat := 397065347470148764318747

theorem tailTrace_773282 : CollatzResearch.WordTrace tailWord_773282 prefixEnd_773282 397065347470148764318747 := by
  unfold tailWord_773282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050977896134713724098525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18802607723025903264262733 7050977896134713724098525)
  ·
    refine ⟨2644116711050517646536947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7050977896134713724098525 2644116711050517646536947)
    ·
      refine ⟨3966175066575776469805421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644116711050517646536947 3966175066575776469805421)
      ·
        refine ⟨1487315649965916176177033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3966175066575776469805421 1487315649965916176177033)
        ·
          refine ⟨1115486737474437132132775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487315649965916176177033 1115486737474437132132775)
          ·
            refine ⟨1673230106211655698199163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115486737474437132132775 1673230106211655698199163)
            ·
              refine ⟨2509845159317483547298745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673230106211655698199163 2509845159317483547298745)
              ·
                refine ⟨1882383869488112660474059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509845159317483547298745 1882383869488112660474059)
                ·
                  refine ⟨2823575804232168990711089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882383869488112660474059 2823575804232168990711089)
                  ·
                    refine ⟨2117681853174126743033317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2823575804232168990711089 2117681853174126743033317)
                    ·
                      refine ⟨397065347470148764318747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2117681853174126743033317 397065347470148764318747)
                      ·
                        rfl

theorem cell23_773282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_773282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773282 prefixEnd_773282 := by exact prefixLift 773282
  have htrace : WordTrace (prefixWord ++ tailWord_773282) baseStart_773282 baseEnd_773282 := by
    simpa [prefixWord, tailWord_773282, baseEnd_773282] using wordTrace_append hprefix tailTrace_773282
  have hstable : (prefixWord ++ tailWord_773282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773282).length < 2 ^ (prefixWord ++ tailWord_773282).sum := by decide
  have hdescent : baseEnd_773282 < baseStart_773282 := by decide
  rcases family_descends (prefixWord ++ tailWord_773282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773285 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_773285 : Nat := 118140960795 + 773285 * 2 ^ 59
def prefixEnd_773285 : Nat := 4983230072969 + 3 ^ 40 * 773285 * 2
def baseEnd_773285 : Nat := 397066887912112252581233

theorem tailTrace_773285 : CollatzResearch.WordTrace tailWord_773285 prefixEnd_773285 397066887912112252581233 := by
  unfold tailWord_773285
  simp only [CollatzResearch.WordTrace]
  refine ⟨28204021003527986408753309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18802680669018657605835539 28204021003527986408753309)
  ·
    refine ⟨10576507876322994903282491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28204021003527986408753309 10576507876322994903282491)
    ·
      refine ⟨15864761814484492354923737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576507876322994903282491 15864761814484492354923737)
      ·
        refine ⟨11898571360863369266192803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15864761814484492354923737 11898571360863369266192803)
        ·
          refine ⟨17847857041295053899289205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898571360863369266192803 17847857041295053899289205)
          ·
            refine ⟨1673236597621411303058363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17847857041295053899289205 1673236597621411303058363)
            ·
              refine ⟨2509854896432116954587545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673236597621411303058363 2509854896432116954587545)
              ·
                refine ⟨1882391172324087715940659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509854896432116954587545 1882391172324087715940659)
                ·
                  refine ⟨2823586758486131573910989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882391172324087715940659 2823586758486131573910989)
                  ·
                    refine ⟨1058845034432299340216621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823586758486131573910989 1058845034432299340216621)
                    ·
                      refine ⟨397066887912112252581233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058845034432299340216621 397066887912112252581233)
                      ·
                        rfl

theorem cell23_773285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_773285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773285 prefixEnd_773285 := by exact prefixLift 773285
  have htrace : WordTrace (prefixWord ++ tailWord_773285) baseStart_773285 baseEnd_773285 := by
    simpa [prefixWord, tailWord_773285, baseEnd_773285] using wordTrace_append hprefix tailTrace_773285
  have hstable : (prefixWord ++ tailWord_773285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773285).length < 2 ^ (prefixWord ++ tailWord_773285).sum := by decide
  have hdescent : baseEnd_773285 < baseStart_773285 := by decide
  rcases family_descends (prefixWord ++ tailWord_773285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773338 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_773338 : Nat := 118140960795 + 773338 * 2 ^ 59
def prefixEnd_773338 : Nat := 4983230072969 + 3 ^ 40 * 773338 * 2
def baseEnd_773338 : Nat := 397094102386800545218489

theorem tailTrace_773338 : CollatzResearch.WordTrace tailWord_773338 prefixEnd_773338 397094102386800545218489 := by
  unfold tailWord_773338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051488518083994115108167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18803969381557317640288445 7051488518083994115108167)
  ·
    refine ⟨10577232777125991172662251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051488518083994115108167 10577232777125991172662251)
    ·
      refine ⟨15865849165688986758993377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10577232777125991172662251 15865849165688986758993377)
      ·
        refine ⟨11899386874266740069245033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15865849165688986758993377 11899386874266740069245033)
        ·
          refine ⟨8924540155700055051933775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11899386874266740069245033 8924540155700055051933775)
          ·
            refine ⟨13386810233550082577900663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8924540155700055051933775 13386810233550082577900663)
            ·
              refine ⟨20080215350325123866850995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386810233550082577900663 20080215350325123866850995)
              ·
                refine ⟨30120323025487685800276493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20080215350325123866850995 30120323025487685800276493)
                ·
                  refine ⟨11295121134557882175103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30120323025487685800276493 11295121134557882175103685)
                  ·
                    refine ⟨2117835212729602907831941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11295121134557882175103685 2117835212729602907831941)
                    ·
                      refine ⟨397094102386800545218489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2117835212729602907831941 397094102386800545218489)
                      ·
                        rfl

theorem cell23_773338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_773338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773338 prefixEnd_773338 := by exact prefixLift 773338
  have htrace : WordTrace (prefixWord ++ tailWord_773338) baseStart_773338 baseEnd_773338 := by
    simpa [prefixWord, tailWord_773338, baseEnd_773338] using wordTrace_append hprefix tailTrace_773338
  have hstable : (prefixWord ++ tailWord_773338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773338).length < 2 ^ (prefixWord ++ tailWord_773338).sum := by decide
  have hdescent : baseEnd_773338 < baseStart_773338 := by decide
  rcases family_descends (prefixWord ++ tailWord_773338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773359 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 4, 2, 2]
def baseStart_773359 : Nat := 118140960795 + 773359 * 2 ^ 59
def prefixEnd_773359 : Nat := 4983230072969 + 3 ^ 40 * 773359 * 2
def baseEnd_773359 : Nat := 397104885480544963055893

theorem tailTrace_773359 : CollatzResearch.WordTrace tailWord_773359 prefixEnd_773359 397104885480544963055893 := by
  unfold tailWord_773359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28206720005259897046947131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18804480003506598031298087 28206720005259897046947131)
  ·
    refine ⟨42310080007889845570420697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28206720005259897046947131 42310080007889845570420697)
    ·
      refine ⟨31732560005917384177815523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42310080007889845570420697 31732560005917384177815523)
      ·
        refine ⟨47598840008876076266723285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31732560005917384177815523 47598840008876076266723285)
        ·
          refine ⟨1115597812708033037501327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47598840008876076266723285 1115597812708033037501327)
          ·
            refine ⟨1673396719062049556251991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115597812708033037501327 1673396719062049556251991)
            ·
              refine ⟨2510095078593074334377987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673396719062049556251991 2510095078593074334377987)
              ·
                refine ⟨3765142617889611501566981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510095078593074334377987 3765142617889611501566981)
                ·
                  refine ⟨705964240854302156543809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3765142617889611501566981 705964240854302156543809)
                  ·
                    refine ⟨529473180640726617407857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 705964240854302156543809 529473180640726617407857)
                    ·
                      refine ⟨397104885480544963055893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529473180640726617407857 397104885480544963055893)
                      ·
                        rfl

theorem cell23_773359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2, 2].length) (baseStart_773359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773359 prefixEnd_773359 := by exact prefixLift 773359
  have htrace : WordTrace (prefixWord ++ tailWord_773359) baseStart_773359 baseEnd_773359 := by
    simpa [prefixWord, tailWord_773359, baseEnd_773359] using wordTrace_append hprefix tailTrace_773359
  have hstable : (prefixWord ++ tailWord_773359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773359).length < 2 ^ (prefixWord ++ tailWord_773359).sum := by decide
  have hdescent : baseEnd_773359 < baseStart_773359 := by decide
  rcases family_descends (prefixWord ++ tailWord_773359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773375 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_773375 : Nat := 118140960795 + 773375 * 2 ^ 59
def prefixEnd_773375 : Nat := 4983230072969 + 3 ^ 40 * 773375 * 2
def baseEnd_773375 : Nat := 397113101171016900455819

theorem tailTrace_773375 : CollatzResearch.WordTrace tailWord_773375 prefixEnd_773375 397113101171016900455819 := by
  unfold tailWord_773375
  simp only [CollatzResearch.WordTrace]
  refine ⟨28207303573201931779529579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18804869048801287853019719 28207303573201931779529579)
  ·
    refine ⟨42310955359802897669294369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28207303573201931779529579 42310955359802897669294369)
    ·
      refine ⟨31733216519852173251970777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42310955359802897669294369 31733216519852173251970777)
      ·
        refine ⟨23799912389889129938978083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31733216519852173251970777 23799912389889129938978083)
        ·
          refine ⟨35699868584833694908467125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23799912389889129938978083 35699868584833694908467125)
          ·
            refine ⟨3346862679828158897668793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35699868584833694908467125 3346862679828158897668793)
            ·
              refine ⟨2510147009871119173251595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346862679828158897668793 2510147009871119173251595)
              ·
                refine ⟨3765220514806678759877393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510147009871119173251595 3765220514806678759877393)
                ·
                  refine ⟨2823915386105009069908045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765220514806678759877393 2823915386105009069908045)
                  ·
                    refine ⟨1058968269789378401215517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823915386105009069908045 1058968269789378401215517)
                    ·
                      refine ⟨397113101171016900455819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1058968269789378401215517 397113101171016900455819)
                      ·
                        rfl

theorem cell23_773375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_773375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773375 prefixEnd_773375 := by exact prefixLift 773375
  have htrace : WordTrace (prefixWord ++ tailWord_773375) baseStart_773375 baseEnd_773375 := by
    simpa [prefixWord, tailWord_773375, baseEnd_773375] using wordTrace_append hprefix tailTrace_773375
  have hstable : (prefixWord ++ tailWord_773375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773375).length < 2 ^ (prefixWord ++ tailWord_773375).sum := by decide
  have hdescent : baseEnd_773375 < baseStart_773375 := by decide
  rcases family_descends (prefixWord ++ tailWord_773375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773452 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3]
def baseStart_773452 : Nat := 118140960795 + 773452 * 2 ^ 59
def prefixEnd_773452 : Nat := 4983230072969 + 3 ^ 40 * 773452 * 2
def baseEnd_773452 : Nat := 397152639181413099192965

theorem tailTrace_773452 : CollatzResearch.WordTrace tailWord_773452 prefixEnd_773452 397152639181413099192965 := by
  unfold tailWord_773452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105055996961486965041305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18806741329281982620055073 14105055996961486965041305)
  ·
    refine ⟨10578791997721115223780979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14105055996961486965041305 10578791997721115223780979)
    ·
      refine ⟨15868187996581672835671469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578791997721115223780979 15868187996581672835671469)
      ·
        refine ⟨5950570498718127313376801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15868187996581672835671469 5950570498718127313376801)
        ·
          refine ⟨4462927874038595485032601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5950570498718127313376801 4462927874038595485032601)
          ·
            refine ⟨3347195905528946613774451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4462927874038595485032601 3347195905528946613774451)
            ·
              refine ⟨5020793858293419920661677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347195905528946613774451 5020793858293419920661677)
              ·
                refine ⟨1882797696860032470248129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5020793858293419920661677 1882797696860032470248129)
                ·
                  refine ⟨1412098272645024352686097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882797696860032470248129 1412098272645024352686097)
                  ·
                    refine ⟨1059073704483768264514573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412098272645024352686097 1059073704483768264514573)
                    ·
                      refine ⟨397152639181413099192965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059073704483768264514573 397152639181413099192965)
                      ·
                        rfl

theorem cell23_773452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_773452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773452 prefixEnd_773452 := by exact prefixLift 773452
  have htrace : WordTrace (prefixWord ++ tailWord_773452) baseStart_773452 baseEnd_773452 := by
    simpa [prefixWord, tailWord_773452, baseEnd_773452] using wordTrace_append hprefix tailTrace_773452
  have hstable : (prefixWord ++ tailWord_773452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773452).length < 2 ^ (prefixWord ++ tailWord_773452).sum := by decide
  have hdescent : baseEnd_773452 < baseStart_773452 := by decide
  rcases family_descends (prefixWord ++ tailWord_773452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773472 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 6]
def baseStart_773472 : Nat := 118140960795 + 773472 * 2 ^ 59
def prefixEnd_773472 : Nat := 4983230072969 + 3 ^ 40 * 773472 * 2
def baseEnd_773472 : Nat := 44129212088278113438097

theorem tailTrace_773472 : CollatzResearch.WordTrace tailWord_773472 prefixEnd_773472 44129212088278113438097 := by
  unfold tailWord_773472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105420726925258672905335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18807227635900344897207113 14105420726925258672905335)
  ·
    refine ⟨21158131090387888009358003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14105420726925258672905335 21158131090387888009358003)
    ·
      refine ⟨31737196635581832014037005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21158131090387888009358003 31737196635581832014037005)
      ·
        refine ⟨11901448738343187005263877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31737196635581832014037005 11901448738343187005263877)
        ·
          refine ⟨2231521638439347563486977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11901448738343187005263877 2231521638439347563486977)
          ·
            refine ⟨1673641228829510672615233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2231521638439347563486977 1673641228829510672615233)
            ·
              refine ⟨1255230921622133004461425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1673641228829510672615233 1255230921622133004461425)
              ·
                refine ⟨941423191216599753346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255230921622133004461425 941423191216599753346069)
                ·
                  refine ⟨44129212088278113438097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 941423191216599753346069 44129212088278113438097)
                  ·
                    rfl

theorem cell23_773472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_773472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773472 prefixEnd_773472 := by exact prefixLift 773472
  have htrace : WordTrace (prefixWord ++ tailWord_773472) baseStart_773472 baseEnd_773472 := by
    simpa [prefixWord, tailWord_773472, baseEnd_773472] using wordTrace_append hprefix tailTrace_773472
  have hstable : (prefixWord ++ tailWord_773472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773472).length < 2 ^ (prefixWord ++ tailWord_773472).sum := by decide
  have hdescent : baseEnd_773472 < baseStart_773472 := by decide
  rcases family_descends (prefixWord ++ tailWord_773472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773476 : List Nat := [2, 3, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_773476 : Nat := 118140960795 + 773476 * 2 ^ 59
def prefixEnd_773476 : Nat := 4983230072969 + 3 ^ 40 * 773476 * 2
def baseEnd_773476 : Nat := 132388320905707001764285

theorem tailTrace_773476 : CollatzResearch.WordTrace tailWord_773476 prefixEnd_773476 132388320905707001764285 := by
  unfold tailWord_773476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14105493672918013014478141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18807324897224017352637521 14105493672918013014478141)
  ·
    refine ⟨5289560127344254880429303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14105493672918013014478141 5289560127344254880429303)
    ·
      refine ⟨7934340191016382320643955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5289560127344254880429303 7934340191016382320643955)
      ·
        refine ⟨11901510286524573480965933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7934340191016382320643955 11901510286524573480965933)
        ·
          refine ⟨4463066357446715055362225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11901510286524573480965933 4463066357446715055362225)
          ·
            refine ⟨3347299768085036291521669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463066357446715055362225 3347299768085036291521669)
            ·
              refine ⟨627618706515944304660313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3347299768085036291521669 627618706515944304660313)
              ·
                refine ⟨470714029886958228495235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627618706515944304660313 470714029886958228495235)
                ·
                  refine ⟨706071044830437342742853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470714029886958228495235 706071044830437342742853)
                  ·
                    refine ⟨132388320905707001764285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706071044830437342742853 132388320905707001764285)
                    ·
                      rfl

theorem cell23_773476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_773476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773476 prefixEnd_773476 := by exact prefixLift 773476
  have htrace : WordTrace (prefixWord ++ tailWord_773476) baseStart_773476 baseEnd_773476 := by
    simpa [prefixWord, tailWord_773476, baseEnd_773476] using wordTrace_append hprefix tailTrace_773476
  have hstable : (prefixWord ++ tailWord_773476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773476).length < 2 ^ (prefixWord ++ tailWord_773476).sum := by decide
  have hdescent : baseEnd_773476 < baseStart_773476 := by decide
  rcases family_descends (prefixWord ++ tailWord_773476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773509 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 2, 3, 2]
def baseStart_773509 : Nat := 118140960795 + 773509 * 2 ^ 59
def prefixEnd_773509 : Nat := 4983230072969 + 3 ^ 40 * 773509 * 2
def baseEnd_773509 : Nat := 397181907578719376180203

theorem tailTrace_773509 : CollatzResearch.WordTrace tailWord_773509 prefixEnd_773509 397181907578719376180203 := by
  unfold tailWord_773509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212190954716472664907581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18808127303144315109938387 28212190954716472664907581)
  ·
    refine ⟨10579571608018677249340343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28212190954716472664907581 10579571608018677249340343)
    ·
      refine ⟨15869357412028015874010515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579571608018677249340343 15869357412028015874010515)
      ·
        refine ⟨23804036118042023811015773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15869357412028015874010515 23804036118042023811015773)
        ·
          refine ⟨8926513544265758929130915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23804036118042023811015773 8926513544265758929130915)
          ·
            refine ⟨13389770316398638393696373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926513544265758929130915 13389770316398638393696373)
            ·
              refine ⟨1255290967162372349409035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13389770316398638393696373 1255290967162372349409035)
              ·
                refine ⟨1882936450743558524113553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255290967162372349409035 1882936450743558524113553)
                ·
                  refine ⟨1412202338057668893085165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882936450743558524113553 1412202338057668893085165)
                  ·
                    refine ⟨529575876771625834906937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412202338057668893085165 529575876771625834906937)
                    ·
                      refine ⟨397181907578719376180203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529575876771625834906937 397181907578719376180203)
                      ·
                        rfl

theorem cell23_773509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_773509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773509 prefixEnd_773509 := by exact prefixLift 773509
  have htrace : WordTrace (prefixWord ++ tailWord_773509) baseStart_773509 baseEnd_773509 := by
    simpa [prefixWord, tailWord_773509, baseEnd_773509] using wordTrace_append hprefix tailTrace_773509
  have hstable : (prefixWord ++ tailWord_773509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773509).length < 2 ^ (prefixWord ++ tailWord_773509).sum := by decide
  have hdescent : baseEnd_773509 < baseStart_773509 := by decide
  rcases family_descends (prefixWord ++ tailWord_773509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773515 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 6]
def baseStart_773515 : Nat := 118140960795 + 773515 * 2 ^ 59
def prefixEnd_773515 : Nat := 4983230072969 + 3 ^ 40 * 773515 * 2
def baseEnd_773515 : Nat := 132394996154215450901725

theorem tailTrace_773515 : CollatzResearch.WordTrace tailWord_773515 prefixEnd_773515 132394996154215450901725 := by
  unfold tailWord_773515
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212409792694735689625999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18808273195129823793083999 28212409792694735689625999)
  ·
    refine ⟨42318614689042103534438999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28212409792694735689625999 42318614689042103534438999)
    ·
      refine ⟨63477922033563155301658499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42318614689042103534438999 63477922033563155301658499)
      ·
        refine ⟨95216883050344732952487749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63477922033563155301658499 95216883050344732952487749)
        ·
          refine ⟨17853165571939637428591453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95216883050344732952487749 17853165571939637428591453)
          ·
            refine ⟨6694937089477364035721795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17853165571939637428591453 6694937089477364035721795)
            ·
              refine ⟨10042405634216046053582693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694937089477364035721795 10042405634216046053582693)
              ·
                refine ⟨1882951056415508635046755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10042405634216046053582693 1882951056415508635046755)
                ·
                  refine ⟨2824426584623262952570133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882951056415508635046755 2824426584623262952570133)
                  ·
                    refine ⟨132394996154215450901725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2824426584623262952570133 132394996154215450901725)
                    ·
                      rfl

theorem cell23_773515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_773515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773515 prefixEnd_773515 := by exact prefixLift 773515
  have htrace : WordTrace (prefixWord ++ tailWord_773515) baseStart_773515 baseEnd_773515 := by
    simpa [prefixWord, tailWord_773515, baseEnd_773515] using wordTrace_append hprefix tailTrace_773515
  have hstable : (prefixWord ++ tailWord_773515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773515).length < 2 ^ (prefixWord ++ tailWord_773515).sum := by decide
  have hdescent : baseEnd_773515 < baseStart_773515 := by decide
  rcases family_descends (prefixWord ++ tailWord_773515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773516 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 1, 1, 3]
def baseStart_773516 : Nat := 118140960795 + 773516 * 2 ^ 59
def prefixEnd_773516 : Nat := 4983230072969 + 3 ^ 40 * 773516 * 2
def baseEnd_773516 : Nat := 397185501943300848792671

theorem tailTrace_773516 : CollatzResearch.WordTrace tailWord_773516 prefixEnd_773516 397185501943300848792671 := by
  unfold tailWord_773516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106223132845556430206201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18808297510460741906941601 14106223132845556430206201)
  ·
    refine ⟨10579667349634167322654651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14106223132845556430206201 10579667349634167322654651)
    ·
      refine ⟨15869501024451250983981977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579667349634167322654651 15869501024451250983981977)
      ·
        refine ⟨11902125768338438237986483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15869501024451250983981977 11902125768338438237986483)
        ·
          refine ⟨17853188652507657356979725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902125768338438237986483 17853188652507657356979725)
          ·
            refine ⟨6694945744690371508867397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17853188652507657356979725 6694945744690371508867397)
            ·
              refine ⟨1255302327129444657912637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6694945744690371508867397 1255302327129444657912637)
              ·
                refine ⟨470738372673541746717239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255302327129444657912637 470738372673541746717239)
                ·
                  refine ⟨706107559010312620075859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470738372673541746717239 706107559010312620075859)
                  ·
                    refine ⟨1059161338515468930113789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706107559010312620075859 1059161338515468930113789)
                    ·
                      refine ⟨397185501943300848792671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059161338515468930113789 397185501943300848792671)
                      ·
                        rfl

theorem cell23_773516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_773516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773516 prefixEnd_773516 := by exact prefixLift 773516
  have htrace : WordTrace (prefixWord ++ tailWord_773516) baseStart_773516 baseEnd_773516 := by
    simpa [prefixWord, tailWord_773516, baseEnd_773516] using wordTrace_append hprefix tailTrace_773516
  have hstable : (prefixWord ++ tailWord_773516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773516).length < 2 ^ (prefixWord ++ tailWord_773516).sum := by decide
  have hdescent : baseEnd_773516 < baseStart_773516 := by decide
  rcases family_descends (prefixWord ++ tailWord_773516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773549 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_773549 : Nat := 118140960795 + 773549 * 2 ^ 59
def prefixEnd_773549 : Nat := 4983230072969 + 3 ^ 40 * 773549 * 2
def baseEnd_773549 : Nat := 132400815601633073226673

theorem tailTrace_773549 : CollatzResearch.WordTrace tailWord_773549 prefixEnd_773549 132400815601633073226673 := by
  unfold tailWord_773549
  simp only [CollatzResearch.WordTrace]
  refine ⟨28213649874571559496363701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18809099916381039664242467 28213649874571559496363701)
  ·
    refine ⟨2645029675741083702784097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28213649874571559496363701 2645029675741083702784097)
    ·
      refine ⟨1983772256805812777088073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2645029675741083702784097 1983772256805812777088073)
      ·
        refine ⟨1487829192604359582816055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983772256805812777088073 1487829192604359582816055)
        ·
          refine ⟨2231743788906539374224083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487829192604359582816055 2231743788906539374224083)
          ·
            refine ⟨3347615683359809061336125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231743788906539374224083 3347615683359809061336125)
            ·
              refine ⟨1255355881259928398001047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3347615683359809061336125 1255355881259928398001047)
              ·
                refine ⟨1883033821889892597001571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255355881259928398001047 1883033821889892597001571)
                ·
                  refine ⟨2824550732834838895502357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883033821889892597001571 2824550732834838895502357)
                  ·
                    refine ⟨132400815601633073226673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2824550732834838895502357 132400815601633073226673)
                    ·
                      rfl

theorem cell23_773549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_773549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773549 prefixEnd_773549 := by exact prefixLift 773549
  have htrace : WordTrace (prefixWord ++ tailWord_773549) baseStart_773549 baseEnd_773549 := by
    simpa [prefixWord, tailWord_773549, baseEnd_773549] using wordTrace_append hprefix tailTrace_773549
  have hstable : (prefixWord ++ tailWord_773549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773549).length < 2 ^ (prefixWord ++ tailWord_773549).sum := by decide
  have hdescent : baseEnd_773549 < baseStart_773549 := by decide
  rcases family_descends (prefixWord ++ tailWord_773549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773559 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_773559 : Nat := 118140960795 + 773559 * 2 ^ 59
def prefixEnd_773559 : Nat := 4983230072969 + 3 ^ 40 * 773559 * 2
def baseEnd_773559 : Nat := 397207581611444180554973

theorem tailTrace_773559 : CollatzResearch.WordTrace tailWord_773559 prefixEnd_773559 397207581611444180554973 := by
  unfold tailWord_773559
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214014604535331204227731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18809343069690220802818487 28214014604535331204227731)
  ·
    refine ⟨42321021906802996806341597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28214014604535331204227731 42321021906802996806341597)
    ·
      refine ⟨15870383215051123802378099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42321021906802996806341597 15870383215051123802378099)
      ·
        refine ⟨23805574822576685703567149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870383215051123802378099 23805574822576685703567149)
        ·
          refine ⟨8927090558466257138837681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23805574822576685703567149 8927090558466257138837681)
          ·
            refine ⟨6695317918849692854128261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8927090558466257138837681 6695317918849692854128261)
            ·
              refine ⟨1255372109784317410149049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6695317918849692854128261 1255372109784317410149049)
              ·
                refine ⟨941529082338238057611787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255372109784317410149049 941529082338238057611787)
                ·
                  refine ⟨1412293623507357086417681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941529082338238057611787 1412293623507357086417681)
                  ·
                    refine ⟨1059220217630517814813261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412293623507357086417681 1059220217630517814813261)
                    ·
                      refine ⟨397207581611444180554973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059220217630517814813261 397207581611444180554973)
                      ·
                        rfl

theorem cell23_773559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_773559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773559 prefixEnd_773559 := by exact prefixLift 773559
  have htrace : WordTrace (prefixWord ++ tailWord_773559) baseStart_773559 baseEnd_773559 := by
    simpa [prefixWord, tailWord_773559, baseEnd_773559] using wordTrace_append hprefix tailTrace_773559
  have hstable : (prefixWord ++ tailWord_773559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773559).length < 2 ^ (prefixWord ++ tailWord_773559).sum := by decide
  have hdescent : baseEnd_773559 < baseStart_773559 := by decide
  rcases family_descends (prefixWord ++ tailWord_773559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773589 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_773589 : Nat := 118140960795 + 773589 * 2 ^ 59
def prefixEnd_773589 : Nat := 4983230072969 + 3 ^ 40 * 773589 * 2
def baseEnd_773589 : Nat := 397222986031079063179835

theorem tailTrace_773589 : CollatzResearch.WordTrace tailWord_773589 prefixEnd_773589 397222986031079063179835 := by
  unfold tailWord_773589
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215108794426646327819821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810072529617764218546547 28215108794426646327819821)
  ·
    refine ⟨10580665797909992372932433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28215108794426646327819821 10580665797909992372932433)
    ·
      refine ⟨7935499348432494279699325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10580665797909992372932433 7935499348432494279699325)
      ·
        refine ⟨2975812255662185354887247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7935499348432494279699325 2975812255662185354887247)
        ·
          refine ⟨4463718383493278032330871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975812255662185354887247 4463718383493278032330871)
          ·
            refine ⟨6695577575239917048496307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463718383493278032330871 6695577575239917048496307)
            ·
              refine ⟨10043366362859875572744461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695577575239917048496307 10043366362859875572744461)
              ·
                refine ⟨3766262386072453339779173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10043366362859875572744461 3766262386072453339779173)
                ·
                  refine ⟨706174197388585001208595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3766262386072453339779173 706174197388585001208595)
                  ·
                    refine ⟨1059261296082877501812893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706174197388585001208595 1059261296082877501812893)
                    ·
                      refine ⟨397222986031079063179835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059261296082877501812893 397222986031079063179835)
                      ·
                        rfl

theorem cell23_773589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_773589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773589 prefixEnd_773589 := by exact prefixLift 773589
  have htrace : WordTrace (prefixWord ++ tailWord_773589) baseStart_773589 baseEnd_773589 := by
    simpa [prefixWord, tailWord_773589, baseEnd_773589] using wordTrace_append hprefix tailTrace_773589
  have hstable : (prefixWord ++ tailWord_773589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773589).length < 2 ^ (prefixWord ++ tailWord_773589).sum := by decide
  have hdescent : baseEnd_773589 < baseStart_773589 := by decide
  rcases family_descends (prefixWord ++ tailWord_773589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773590 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_773590 : Nat := 118140960795 + 773590 * 2 ^ 59
def prefixEnd_773590 : Nat := 4983230072969 + 3 ^ 40 * 773590 * 2
def baseEnd_773590 : Nat := 397223499511733559267331

theorem tailTrace_773590 : CollatzResearch.WordTrace tailWord_773590 prefixEnd_773590 397223499511733559267331 := by
  unfold tailWord_773590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763446579213938968662889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18810096844948682332404149 1763446579213938968662889)
  ·
    refine ⟨1322584934410454226497167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1763446579213938968662889 1322584934410454226497167)
    ·
      refine ⟨1983877401615681339745751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1322584934410454226497167 1983877401615681339745751)
      ·
        refine ⟨2975816102423522009618627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983877401615681339745751 2975816102423522009618627)
        ·
          refine ⟨4463724153635283014427941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975816102423522009618627 4463724153635283014427941)
          ·
            refine ⟨836948278806615565205239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4463724153635283014427941 836948278806615565205239)
            ·
              refine ⟨1255422418209923347807859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836948278806615565205239 1255422418209923347807859)
              ·
                refine ⟨1883133627314885021711789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255422418209923347807859 1883133627314885021711789)
                ·
                  refine ⟨706175110243081883141921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1883133627314885021711789 706175110243081883141921)
                  ·
                    refine ⟨529631332682311412356441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 706175110243081883141921 529631332682311412356441)
                    ·
                      refine ⟨397223499511733559267331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529631332682311412356441 397223499511733559267331)
                      ·
                        rfl

theorem cell23_773590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_773590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773590 prefixEnd_773590 := by exact prefixLift 773590
  have htrace : WordTrace (prefixWord ++ tailWord_773590) baseStart_773590 baseEnd_773590 := by
    simpa [prefixWord, tailWord_773590, baseEnd_773590] using wordTrace_append hprefix tailTrace_773590
  have hstable : (prefixWord ++ tailWord_773590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773590).length < 2 ^ (prefixWord ++ tailWord_773590).sum := by decide
  have hdescent : baseEnd_773590 < baseStart_773590 := by decide
  rcases family_descends (prefixWord ++ tailWord_773590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773595 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_773595 : Nat := 118140960795 + 773595 * 2 ^ 59
def prefixEnd_773595 : Nat := 4983230072969 + 3 ^ 40 * 773595 * 2
def baseEnd_773595 : Nat := 397226066915006039704807

theorem tailTrace_773595 : CollatzResearch.WordTrace tailWord_773595 prefixEnd_773595 397226066915006039704807 := by
  unfold tailWord_773595
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215327632404909352538239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810218421603272901692159 28215327632404909352538239)
  ·
    refine ⟨42322991448607364028807359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28215327632404909352538239 42322991448607364028807359)
    ·
      refine ⟨63484487172911046043211039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42322991448607364028807359 63484487172911046043211039)
      ·
        refine ⟨95226730759366569064816559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63484487172911046043211039 95226730759366569064816559)
        ·
          refine ⟨142840096139049853597224839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95226730759366569064816559 142840096139049853597224839)
          ·
            refine ⟨214260144208574780395837259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142840096139049853597224839 214260144208574780395837259)
            ·
              refine ⟨321390216312862170593755889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214260144208574780395837259 321390216312862170593755889)
              ·
                refine ⟨241042662234646627945316917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321390216312862170593755889 241042662234646627945316917)
                ·
                  refine ⟨22597749584498121369873461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241042662234646627945316917 22597749584498121369873461)
                  ·
                    refine ⟨2118539023546698878425637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22597749584498121369873461 2118539023546698878425637)
                    ·
                      refine ⟨397226066915006039704807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2118539023546698878425637 397226066915006039704807)
                      ·
                        rfl

theorem cell23_773595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_773595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773595 prefixEnd_773595 := by exact prefixLift 773595
  have htrace : WordTrace (prefixWord ++ tailWord_773595) baseStart_773595 baseEnd_773595 := by
    simpa [prefixWord, tailWord_773595, baseEnd_773595] using wordTrace_append hprefix tailTrace_773595
  have hstable : (prefixWord ++ tailWord_773595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773595).length < 2 ^ (prefixWord ++ tailWord_773595).sum := by decide
  have hdescent : baseEnd_773595 < baseStart_773595 := by decide
  rcases family_descends (prefixWord ++ tailWord_773595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773599 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 3, 3, 2]
def baseStart_773599 : Nat := 118140960795 + 773599 * 2 ^ 59
def prefixEnd_773599 : Nat := 4983230072969 + 3 ^ 40 * 773599 * 2
def baseEnd_773599 : Nat := 397228120837624024054789

theorem tailTrace_773599 : CollatzResearch.WordTrace tailWord_773599 prefixEnd_773599 397228120837624024054789 := by
  unfold tailWord_773599
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215473524390418035683851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18810315682926945357122567 28215473524390418035683851)
  ·
    refine ⟨42323210286585627053525777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28215473524390418035683851 42323210286585627053525777)
    ·
      refine ⟨31742407714939220290144333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42323210286585627053525777 31742407714939220290144333)
      ·
        refine ⟨11903402893102207608804125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31742407714939220290144333 11903402893102207608804125)
        ·
          refine ⟨4463776084913327853301547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11903402893102207608804125 4463776084913327853301547)
          ·
            refine ⟨6695664127369991779952321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463776084913327853301547 6695664127369991779952321)
            ·
              refine ⟨5021748095527493834964241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695664127369991779952321 5021748095527493834964241)
              ·
                refine ⟨3766311071645620376223181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021748095527493834964241 3766311071645620376223181)
                ·
                  refine ⟨1412366651867107641083693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3766311071645620376223181 1412366651867107641083693)
                  ·
                    refine ⟨529637494450165365406385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412366651867107641083693 529637494450165365406385)
                    ·
                      refine ⟨397228120837624024054789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529637494450165365406385 397228120837624024054789)
                      ·
                        rfl

theorem cell23_773599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_773599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773599 prefixEnd_773599 := by exact prefixLift 773599
  have htrace : WordTrace (prefixWord ++ tailWord_773599) baseStart_773599 baseEnd_773599 := by
    simpa [prefixWord, tailWord_773599, baseEnd_773599] using wordTrace_append hprefix tailTrace_773599
  have hstable : (prefixWord ++ tailWord_773599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773599).length < 2 ^ (prefixWord ++ tailWord_773599).sum := by decide
  have hdescent : baseEnd_773599 < baseStart_773599 := by decide
  rcases family_descends (prefixWord ++ tailWord_773599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773616 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2]
def baseStart_773616 : Nat := 118140960795 + 773616 * 2 ^ 59
def prefixEnd_773616 : Nat := 4983230072969 + 3 ^ 40 * 773616 * 2
def baseEnd_773616 : Nat := 397236850008750457542211

theorem tailTrace_773616 : CollatzResearch.WordTrace tailWord_773616 prefixEnd_773616 397236850008750457542211 := by
  unfold tailWord_773616
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108046782664414969526351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18810729043552553292701801 14108046782664414969526351)
  ·
    refine ⟨21162070173996622454289527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14108046782664414969526351 21162070173996622454289527)
    ·
      refine ⟨31743105260994933681434291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162070173996622454289527 31743105260994933681434291)
      ·
        refine ⟨47614657891492400522151437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31743105260994933681434291 47614657891492400522151437)
        ·
          refine ⟨17855496709309650195806789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47614657891492400522151437 17855496709309650195806789)
          ·
            refine ⟨3347905632995559411713773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17855496709309650195806789 3347905632995559411713773)
            ·
              refine ⟨1255464612373334779392665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3347905632995559411713773 1255464612373334779392665)
              ·
                refine ⟨941598459280001084544499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255464612373334779392665 941598459280001084544499)
                ·
                  refine ⟨1412397688920001626816749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941598459280001084544499 1412397688920001626816749)
                  ·
                    refine ⟨529649133345000610056281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412397688920001626816749 529649133345000610056281)
                    ·
                      refine ⟨397236850008750457542211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529649133345000610056281 397236850008750457542211)
                      ·
                        rfl

theorem cell23_773616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2].length) (baseStart_773616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773616 prefixEnd_773616 := by exact prefixLift 773616
  have htrace : WordTrace (prefixWord ++ tailWord_773616) baseStart_773616 baseEnd_773616 := by
    simpa [prefixWord, tailWord_773616, baseEnd_773616] using wordTrace_append hprefix tailTrace_773616
  have hstable : (prefixWord ++ tailWord_773616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773616).length < 2 ^ (prefixWord ++ tailWord_773616).sum := by decide
  have hdescent : baseEnd_773616 < baseStart_773616 := by decide
  rcases family_descends (prefixWord ++ tailWord_773616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773629 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 3, 4, 2]
def baseStart_773629 : Nat := 118140960795 + 773629 * 2 ^ 59
def prefixEnd_773629 : Nat := 4983230072969 + 3 ^ 40 * 773629 * 2
def baseEnd_773629 : Nat := 397243525257258906679651

theorem tailTrace_773629 : CollatzResearch.WordTrace tailWord_773629 prefixEnd_773629 397243525257258906679651 := by
  unfold tailWord_773629
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216567714281733159275941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18811045142854488772850627 28216567714281733159275941)
  ·
    refine ⟨5290606446427824967364239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28216567714281733159275941 5290606446427824967364239)
    ·
      refine ⟨7935909669641737451046359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5290606446427824967364239 7935909669641737451046359)
      ·
        refine ⟨11903864504462606176569539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935909669641737451046359 11903864504462606176569539)
        ·
          refine ⟨17855796756693909264854309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903864504462606176569539 17855796756693909264854309)
          ·
            refine ⟨3347961891880107987160183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17855796756693909264854309 3347961891880107987160183)
            ·
              refine ⟨5021942837820161980740275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347961891880107987160183 5021942837820161980740275)
              ·
                refine ⟨7532914256730242971110413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021942837820161980740275 7532914256730242971110413)
                ·
                  refine ⟨2824842846273841114166405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7532914256730242971110413 2824842846273841114166405)
                  ·
                    refine ⟨529658033676345208906201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2824842846273841114166405 529658033676345208906201)
                    ·
                      refine ⟨397243525257258906679651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 529658033676345208906201 397243525257258906679651)
                      ·
                        rfl

theorem cell23_773629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_773629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773629 prefixEnd_773629 := by exact prefixLift 773629
  have htrace : WordTrace (prefixWord ++ tailWord_773629) baseStart_773629 baseEnd_773629 := by
    simpa [prefixWord, tailWord_773629, baseEnd_773629] using wordTrace_append hprefix tailTrace_773629
  have hstable : (prefixWord ++ tailWord_773629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773629).length < 2 ^ (prefixWord ++ tailWord_773629).sum := by decide
  have hdescent : baseEnd_773629 < baseStart_773629 := by decide
  rcases family_descends (prefixWord ++ tailWord_773629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773635 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 11]
def baseStart_773635 : Nat := 118140960795 + 773635 * 2 ^ 59
def prefixEnd_773635 : Nat := 4983230072969 + 3 ^ 40 * 773635 * 2
def baseEnd_773635 : Nat := 44138511793465098133847

theorem tailTrace_773635 : CollatzResearch.WordTrace tailWord_773635 prefixEnd_773635 44138511793465098133847 := by
  unfold tailWord_773635
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216786552259996183994359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18811191034839997455996239 28216786552259996183994359)
  ·
    refine ⟨42325179828389994275991539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28216786552259996183994359 42325179828389994275991539)
    ·
      refine ⟨63487769742584991413987309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42325179828389994275991539 63487769742584991413987309)
      ·
        refine ⟨23807913653469371780245241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63487769742584991413987309 23807913653469371780245241)
        ·
          refine ⟨17855935240102028835183931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23807913653469371780245241 17855935240102028835183931)
          ·
            refine ⟨26783902860153043252775897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17855935240102028835183931 26783902860153043252775897)
            ·
              refine ⟨20087927145114782439581923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26783902860153043252775897 20087927145114782439581923)
              ·
                refine ⟨30131890717672173659372885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20087927145114782439581923 30131890717672173659372885)
                ·
                  refine ⟨44138511793465098133847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 30131890717672173659372885 44138511793465098133847)
                  ·
                    rfl

theorem cell23_773635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 11].length) (baseStart_773635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773635 prefixEnd_773635 := by exact prefixLift 773635
  have htrace : WordTrace (prefixWord ++ tailWord_773635) baseStart_773635 baseEnd_773635 := by
    simpa [prefixWord, tailWord_773635, baseEnd_773635] using wordTrace_append hprefix tailTrace_773635
  have hstable : (prefixWord ++ tailWord_773635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773635).length < 2 ^ (prefixWord ++ tailWord_773635).sum := by decide
  have hdescent : baseEnd_773635 < baseStart_773635 := by decide
  rcases family_descends (prefixWord ++ tailWord_773635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773729 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 3, 4]
def baseStart_773729 : Nat := 118140960795 + 773729 * 2 ^ 59
def prefixEnd_773729 : Nat := 4983230072969 + 3 ^ 40 * 773729 * 2
def baseEnd_773729 : Nat := 132431624440902838476397

theorem tailTrace_773729 : CollatzResearch.WordTrace tailWord_773729 prefixEnd_773729 132431624440902838476397 := by
  unfold tailWord_773729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220215013919450237916241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18813476675946300158610827 28220215013919450237916241)
  ·
    refine ⟨21165161260439587678437181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28220215013919450237916241 21165161260439587678437181)
    ·
      refine ⟨7936935472664845379413943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21165161260439587678437181 7936935472664845379413943)
      ·
        refine ⟨11905403208997268069120915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936935472664845379413943 11905403208997268069120915)
        ·
          refine ⟨17858104813495902103681373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905403208997268069120915 17858104813495902103681373)
          ·
            refine ⟨6696789305060963288880515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17858104813495902103681373 6696789305060963288880515)
            ·
              refine ⟨10045183957591444933320773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696789305060963288880515 10045183957591444933320773)
              ·
                refine ⟨1883471992048395924997645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10045183957591444933320773 1883471992048395924997645)
                ·
                  refine ⟨706301997018148471874117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1883471992048395924997645 706301997018148471874117)
                  ·
                    refine ⟨132431624440902838476397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706301997018148471874117 132431624440902838476397)
                    ·
                      rfl

theorem cell23_773729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_773729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773729 prefixEnd_773729 := by exact prefixLift 773729
  have htrace : WordTrace (prefixWord ++ tailWord_773729) baseStart_773729 baseEnd_773729 := by
    simpa [prefixWord, tailWord_773729, baseEnd_773729] using wordTrace_append hprefix tailTrace_773729
  have hstable : (prefixWord ++ tailWord_773729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773729).length < 2 ^ (prefixWord ++ tailWord_773729).sum := by decide
  have hdescent : baseEnd_773729 < baseStart_773729 := by decide
  rcases family_descends (prefixWord ++ tailWord_773729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773814 : List Nat := [5, 1, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_773814 : Nat := 118140960795 + 773814 * 2 ^ 59
def prefixEnd_773814 : Nat := 4983230072969 + 3 ^ 40 * 773814 * 2
def baseEnd_773814 : Nat := 132446173059446894288767

theorem tailTrace_773814 : CollatzResearch.WordTrace tailWord_773814 prefixEnd_773814 132446173059446894288767 := by
  unfold tailWord_773814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763957201163219359672531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18815543479074339836506997 1763957201163219359672531)
  ·
    refine ⟨2645935801744829039508797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763957201163219359672531 2645935801744829039508797)
    ·
      refine ⟨992225925654310889815799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2645935801744829039508797 992225925654310889815799)
      ·
        refine ⟨1488338888481466334723699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992225925654310889815799 1488338888481466334723699)
        ·
          refine ⟨2232508332722199502085549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488338888481466334723699 2232508332722199502085549)
          ·
            refine ⟨837190624770824813282081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2232508332722199502085549 837190624770824813282081)
            ·
              refine ⟨627892968578118609961561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837190624770824813282081 627892968578118609961561)
              ·
                refine ⟨470919726433588957471171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627892968578118609961561 470919726433588957471171)
                ·
                  refine ⟨706379589650383436206757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470919726433588957471171 706379589650383436206757)
                  ·
                    refine ⟨132446173059446894288767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706379589650383436206757 132446173059446894288767)
                    ·
                      rfl

theorem cell23_773814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_773814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773814 prefixEnd_773814 := by exact prefixLift 773814
  have htrace : WordTrace (prefixWord ++ tailWord_773814) baseStart_773814 baseEnd_773814 := by
    simpa [prefixWord, tailWord_773814, baseEnd_773814] using wordTrace_append hprefix tailTrace_773814
  have hstable : (prefixWord ++ tailWord_773814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773814).length < 2 ^ (prefixWord ++ tailWord_773814).sum := by decide
  have hdescent : baseEnd_773814 < baseStart_773814 := by decide
  rcases family_descends (prefixWord ++ tailWord_773814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773819 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 4, 4]
def baseStart_773819 : Nat := 118140960795 + 773819 * 2 ^ 59
def prefixEnd_773819 : Nat := 4983230072969 + 3 ^ 40 * 773819 * 2
def baseEnd_773819 : Nat := 132447028860537721101259

theorem tailTrace_773819 : CollatzResearch.WordTrace tailWord_773819 prefixEnd_773819 132447028860537721101259 := by
  unfold tailWord_773819
  simp only [CollatzResearch.WordTrace]
  refine ⟨28223497583593395608692511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18815665055728930405795007 28223497583593395608692511)
  ·
    refine ⟨42335246375390093413038767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28223497583593395608692511 42335246375390093413038767)
    ·
      refine ⟨63502869563085140119558151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42335246375390093413038767 63502869563085140119558151)
      ·
        refine ⟨95254304344627710179337227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63502869563085140119558151 95254304344627710179337227)
        ·
          refine ⟨142881456516941565269005841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95254304344627710179337227 142881456516941565269005841)
          ·
            refine ⟨107161092387706173951754381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142881456516941565269005841 107161092387706173951754381)
            ·
              refine ⟨40185409645389815231907893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107161092387706173951754381 40185409645389815231907893)
              ·
                refine ⟨3767382154255295177991365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40185409645389815231907893 3767382154255295177991365)
                ·
                  refine ⟨706384153922867845873381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3767382154255295177991365 706384153922867845873381)
                  ·
                    refine ⟨132447028860537721101259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706384153922867845873381 132447028860537721101259)
                    ·
                      rfl

theorem cell23_773819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 4].length) (baseStart_773819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773819 prefixEnd_773819 := by exact prefixLift 773819
  have htrace : WordTrace (prefixWord ++ tailWord_773819) baseStart_773819 baseEnd_773819 := by
    simpa [prefixWord, tailWord_773819, baseEnd_773819] using wordTrace_append hprefix tailTrace_773819
  have hstable : (prefixWord ++ tailWord_773819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773819).length < 2 ^ (prefixWord ++ tailWord_773819).sum := by decide
  have hdescent : baseEnd_773819 < baseStart_773819 := by decide
  rcases family_descends (prefixWord ++ tailWord_773819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773820 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_773820 : Nat := 118140960795 + 773820 * 2 ^ 59
def prefixEnd_773820 : Nat := 4983230072969 + 3 ^ 40 * 773820 * 2
def baseEnd_773820 : Nat := 397341600062267659391273

theorem tailTrace_773820 : CollatzResearch.WordTrace tailWord_773820 prefixEnd_773820 397341600062267659391273 := by
  unfold tailWord_773820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14111767028294886389739457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18815689371059848519652609 14111767028294886389739457)
  ·
    refine ⟨10583825271221164792304593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14111767028294886389739457 10583825271221164792304593)
    ·
      refine ⟨7937868953415873594228445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10583825271221164792304593 7937868953415873594228445)
      ·
        refine ⟨2976700857530952597835667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7937868953415873594228445 2976700857530952597835667)
        ·
          refine ⟨4465051286296428896753501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976700857530952597835667 4465051286296428896753501)
          ·
            refine ⟨1674394232361160836282563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4465051286296428896753501 1674394232361160836282563)
            ·
              refine ⟨2511591348541741254423845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674394232361160836282563 2511591348541741254423845)
              ·
                refine ⟨470923377851576485204471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2511591348541741254423845 470923377851576485204471)
                ·
                  refine ⟨706385066777364727806707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470923377851576485204471 706385066777364727806707)
                  ·
                    refine ⟨1059577600166047091710061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706385066777364727806707 1059577600166047091710061)
                    ·
                      refine ⟨397341600062267659391273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059577600166047091710061 397341600062267659391273)
                      ·
                        rfl

theorem cell23_773820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_773820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773820 prefixEnd_773820 := by exact prefixLift 773820
  have htrace : WordTrace (prefixWord ++ tailWord_773820) baseStart_773820 baseEnd_773820 := by
    simpa [prefixWord, tailWord_773820, baseEnd_773820] using wordTrace_append hprefix tailTrace_773820
  have hstable : (prefixWord ++ tailWord_773820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773820).length < 2 ^ (prefixWord ++ tailWord_773820).sum := by decide
  have hdescent : baseEnd_773820 < baseStart_773820 := by decide
  rcases family_descends (prefixWord ++ tailWord_773820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773899 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_773899 : Nat := 118140960795 + 773899 * 2 ^ 59
def prefixEnd_773899 : Nat := 4983230072969 + 3 ^ 40 * 773899 * 2
def baseEnd_773899 : Nat := 397382165033972850303409

theorem tailTrace_773899 : CollatzResearch.WordTrace tailWord_773899 prefixEnd_773899 397382165033972850303409 := by
  unfold tailWord_773899
  simp only [CollatzResearch.WordTrace]
  refine ⟨28226415423303569271604751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18817610282202379514403167 28226415423303569271604751)
  ·
    refine ⟨42339623134955353907407127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28226415423303569271604751 42339623134955353907407127)
    ·
      refine ⟨63509434702433030861110691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42339623134955353907407127 63509434702433030861110691)
      ·
        refine ⟨95264152053649546291666037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63509434702433030861110691 95264152053649546291666037)
        ·
          refine ⟨8931014255029644964843691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95264152053649546291666037 8931014255029644964843691)
          ·
            refine ⟨13396521382544467447265537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8931014255029644964843691 13396521382544467447265537)
            ·
              refine ⟨10047391036908350585449153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13396521382544467447265537 10047391036908350585449153)
              ·
                refine ⟨7535543277681262939086865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10047391036908350585449153 7535543277681262939086865)
                ·
                  refine ⟨5651657458260947204315149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535543277681262939086865 5651657458260947204315149)
                  ·
                    refine ⟨2119371546847855201618181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5651657458260947204315149 2119371546847855201618181)
                    ·
                      refine ⟨397382165033972850303409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2119371546847855201618181 397382165033972850303409)
                      ·
                        rfl

theorem cell23_773899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_773899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773899 prefixEnd_773899 := by exact prefixLift 773899
  have htrace : WordTrace (prefixWord ++ tailWord_773899) baseStart_773899 baseEnd_773899 := by
    simpa [prefixWord, tailWord_773899, baseEnd_773899] using wordTrace_append hprefix tailTrace_773899
  have hstable : (prefixWord ++ tailWord_773899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773899).length < 2 ^ (prefixWord ++ tailWord_773899).sum := by decide
  have hdescent : baseEnd_773899 < baseStart_773899 := by decide
  rcases family_descends (prefixWord ++ tailWord_773899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773966 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_773966 : Nat := 118140960795 + 773966 * 2 ^ 59
def prefixEnd_773966 : Nat := 4983230072969 + 3 ^ 40 * 773966 * 2
def baseEnd_773966 : Nat := 397416568237824088165601

theorem tailTrace_773966 : CollatzResearch.WordTrace tailWord_773966 prefixEnd_773966 397416568237824088165601 := by
  unfold tailWord_773966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528607389257604964286719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18819239409373893142862501 3528607389257604964286719)
  ·
    refine ⟨5292911083886407446430079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3528607389257604964286719 5292911083886407446430079)
    ·
      refine ⟨7939366625829611169645119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292911083886407446430079 7939366625829611169645119)
      ·
        refine ⟨11909049938744416754467679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939366625829611169645119 11909049938744416754467679)
        ·
          refine ⟨17863574908116625131701519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909049938744416754467679 17863574908116625131701519)
          ·
            refine ⟨26795362362174937697552279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17863574908116625131701519 26795362362174937697552279)
            ·
              refine ⟨40193043543262406546328419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26795362362174937697552279 40193043543262406546328419)
              ·
                refine ⟨60289565314893609819492629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40193043543262406546328419 60289565314893609819492629)
                ·
                  refine ⟨2826073374135637960288717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60289565314893609819492629 2826073374135637960288717)
                  ·
                    refine ⟨1059777515300864235108269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2826073374135637960288717 1059777515300864235108269)
                    ·
                      refine ⟨397416568237824088165601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1059777515300864235108269 397416568237824088165601)
                      ·
                        rfl

theorem cell23_773966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_773966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773966 prefixEnd_773966 := by exact prefixLift 773966
  have htrace : WordTrace (prefixWord ++ tailWord_773966) baseStart_773966 baseEnd_773966 := by
    simpa [prefixWord, tailWord_773966, baseEnd_773966] using wordTrace_append hprefix tailTrace_773966
  have hstable : (prefixWord ++ tailWord_773966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773966).length < 2 ^ (prefixWord ++ tailWord_773966).sum := by decide
  have hdescent : baseEnd_773966 < baseStart_773966 := by decide
  rcases family_descends (prefixWord ++ tailWord_773966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773996 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 5]
def baseStart_773996 : Nat := 118140960795 + 773996 * 2 ^ 59
def prefixEnd_773996 : Nat := 4983230072969 + 3 ^ 40 * 773996 * 2
def baseEnd_773996 : Nat := 397431972657458970790463

theorem tailTrace_773996 : CollatzResearch.WordTrace tailWord_773996 prefixEnd_773996 397431972657458970790463 := by
  unfold tailWord_773996
  simp only [CollatzResearch.WordTrace]
  refine ⟨14114976651976077418942921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18819968869301436558590561 14114976651976077418942921)
  ·
    refine ⟨10586232488982058064207191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14114976651976077418942921 10586232488982058064207191)
    ·
      refine ⟨15879348733473087096310787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10586232488982058064207191 15879348733473087096310787)
      ·
        refine ⟨23819023100209630644466181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15879348733473087096310787 23819023100209630644466181)
        ·
          refine ⟨4466066831289305745837409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23819023100209630644466181 4466066831289305745837409)
          ·
            refine ⟨3349550123466979309378057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4466066831289305745837409 3349550123466979309378057)
            ·
              refine ⟨2512162592600234482033543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349550123466979309378057 2512162592600234482033543)
              ·
                refine ⟨3768243888900351723050315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512162592600234482033543 3768243888900351723050315)
                ·
                  refine ⟨5652365833350527584575473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768243888900351723050315 5652365833350527584575473)
                  ·
                    refine ⟨4239274375012895688431605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5652365833350527584575473 4239274375012895688431605)
                    ·
                      refine ⟨397431972657458970790463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4239274375012895688431605 397431972657458970790463)
                      ·
                        rfl

theorem cell23_773996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_773996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773996 prefixEnd_773996 := by exact prefixLift 773996
  have htrace : WordTrace (prefixWord ++ tailWord_773996) baseStart_773996 baseEnd_773996 := by
    simpa [prefixWord, tailWord_773996, baseEnd_773996] using wordTrace_append hprefix tailTrace_773996
  have hstable : (prefixWord ++ tailWord_773996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773996).length < 2 ^ (prefixWord ++ tailWord_773996).sum := by decide
  have hdescent : baseEnd_773996 < baseStart_773996 := by decide
  rcases family_descends (prefixWord ++ tailWord_773996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_773999 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 8]
def baseStart_773999 : Nat := 118140960795 + 773999 * 2 ^ 59
def prefixEnd_773999 : Nat := 4983230072969 + 3 ^ 40 * 773999 * 2
def baseEnd_773999 : Nat := 132477837699807486350983

theorem tailTrace_773999 : CollatzResearch.WordTrace tailWord_773999 prefixEnd_773999 132477837699807486350983 := by
  unfold tailWord_773999
  simp only [CollatzResearch.WordTrace]
  refine ⟨28230062722941286350245051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18820041815294190900163367 28230062722941286350245051)
  ·
    refine ⟨42345094084411929525367577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28230062722941286350245051 42345094084411929525367577)
    ·
      refine ⟨31758820563308947144025683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42345094084411929525367577 31758820563308947144025683)
      ·
        refine ⟨47638230844963420716038525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31758820563308947144025683 47638230844963420716038525)
        ·
          refine ⟨17864336566861282768514447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47638230844963420716038525 17864336566861282768514447)
          ·
            refine ⟨26796504850291924152771671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17864336566861282768514447 26796504850291924152771671)
            ·
              refine ⟨40194757275437886229157507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26796504850291924152771671 40194757275437886229157507)
              ·
                refine ⟨60292135913156829343736261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40194757275437886229157507 60292135913156829343736261)
                ·
                  refine ⟨11304775483716905501950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60292135913156829343736261 11304775483716905501950549)
                  ·
                    refine ⟨132477837699807486350983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11304775483716905501950549 132477837699807486350983)
                    ·
                      rfl

theorem cell23_773999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_773999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_773999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_773999 prefixEnd_773999 := by exact prefixLift 773999
  have htrace : WordTrace (prefixWord ++ tailWord_773999) baseStart_773999 baseEnd_773999 := by
    simpa [prefixWord, tailWord_773999, baseEnd_773999] using wordTrace_append hprefix tailTrace_773999
  have hstable : (prefixWord ++ tailWord_773999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_773999).length < 2 ^ (prefixWord ++ tailWord_773999).sum := by decide
  have hdescent : baseEnd_773999 < baseStart_773999 := by decide
  rcases family_descends (prefixWord ++ tailWord_773999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774023 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_774023 : Nat := 118140960795 + 774023 * 2 ^ 59
def prefixEnd_774023 : Nat := 4983230072969 + 3 ^ 40 * 774023 * 2
def baseEnd_774023 : Nat := 397445836635130365152839

theorem tailTrace_774023 : CollatzResearch.WordTrace tailWord_774023 prefixEnd_774023 397445836635130365152839 := by
  unfold tailWord_774023
  simp only [CollatzResearch.WordTrace]
  refine ⟨28230938074854338449118723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18820625383236225632745815 28230938074854338449118723)
  ·
    refine ⟨42346407112281507673678085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28230938074854338449118723 42346407112281507673678085)
    ·
      refine ⟨7939951333552782688814641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42346407112281507673678085 7939951333552782688814641)
      ·
        refine ⟨5954963500164587016610981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7939951333552782688814641 5954963500164587016610981)
        ·
          refine ⟨1116555656280860065614559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5954963500164587016610981 1116555656280860065614559)
          ·
            refine ⟨1674833484421290098421839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116555656280860065614559 1674833484421290098421839)
            ·
              refine ⟨2512250226631935147632759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674833484421290098421839 2512250226631935147632759)
              ·
                refine ⟨3768375339947902721449139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512250226631935147632759 3768375339947902721449139)
                ·
                  refine ⟨5652563009921854082173709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3768375339947902721449139 5652563009921854082173709)
                  ·
                    refine ⟨2119711128720695280815141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5652563009921854082173709 2119711128720695280815141)
                    ·
                      refine ⟨397445836635130365152839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2119711128720695280815141 397445836635130365152839)
                      ·
                        rfl

theorem cell23_774023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_774023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774023 prefixEnd_774023 := by exact prefixLift 774023
  have htrace : WordTrace (prefixWord ++ tailWord_774023) baseStart_774023 baseEnd_774023 := by
    simpa [prefixWord, tailWord_774023, baseEnd_774023] using wordTrace_append hprefix tailTrace_774023
  have hstable : (prefixWord ++ tailWord_774023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774023).length < 2 ^ (prefixWord ++ tailWord_774023).sum := by decide
  have hdescent : baseEnd_774023 < baseStart_774023 := by decide
  rcases family_descends (prefixWord ++ tailWord_774023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774063 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 6]
def baseStart_774063 : Nat := 118140960795 + 774063 * 2 ^ 59
def prefixEnd_774063 : Nat := 4983230072969 + 3 ^ 40 * 774063 * 2
def baseEnd_774063 : Nat := 44162930651256689850295

theorem tailTrace_774063 : CollatzResearch.WordTrace tailWord_774063 prefixEnd_774063 44162930651256689850295 := by
  unfold tailWord_774063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232396994709425280574843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18821597996472950187049895 28232396994709425280574843)
  ·
    refine ⟨42348595492064137920862265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28232396994709425280574843 42348595492064137920862265)
    ·
      refine ⟨31761446619048103440646699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42348595492064137920862265 31761446619048103440646699)
      ·
        refine ⟨47642169928572155160970049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761446619048103440646699 47642169928572155160970049)
        ·
          refine ⟨35731627446429116370727537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47642169928572155160970049 35731627446429116370727537)
          ·
            refine ⟨26798720584821837278045653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35731627446429116370727537 26798720584821837278045653)
            ·
              refine ⟨628095013706761811204195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26798720584821837278045653 628095013706761811204195)
              ·
                refine ⟨942142520560142716806293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628095013706761811204195 942142520560142716806293)
                ·
                  refine ⟨44162930651256689850295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 942142520560142716806293 44162930651256689850295)
                  ·
                    rfl

theorem cell23_774063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 6].length) (baseStart_774063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774063 prefixEnd_774063 := by exact prefixLift 774063
  have htrace : WordTrace (prefixWord ++ tailWord_774063) baseStart_774063 baseEnd_774063 := by
    simpa [prefixWord, tailWord_774063, baseEnd_774063] using wordTrace_append hprefix tailTrace_774063
  have hstable : (prefixWord ++ tailWord_774063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774063).length < 2 ^ (prefixWord ++ tailWord_774063).sum := by decide
  have hdescent : baseEnd_774063 < baseStart_774063 := by decide
  rcases family_descends (prefixWord ++ tailWord_774063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774114 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 6]
def baseStart_774114 : Nat := 118140960795 + 774114 * 2 ^ 59
def prefixEnd_774114 : Nat := 4983230072969 + 3 ^ 40 * 774114 * 2
def baseEnd_774114 : Nat := 44165840374965501012769

theorem tailTrace_774114 : CollatzResearch.WordTrace tailWord_774114 prefixEnd_774114 44165840374965501012769 := by
  unfold tailWord_774114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058564279381165247670349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18822838078349773993787597 7058564279381165247670349)
  ·
    refine ⟨2646961604767936967876381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7058564279381165247670349 2646961604767936967876381)
    ·
      refine ⟨992610601787976362953643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2646961604767936967876381 992610601787976362953643)
      ·
        refine ⟨1488915902681964544430465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992610601787976362953643 1488915902681964544430465)
        ·
          refine ⟨1116686927011473408322849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488915902681964544430465 1116686927011473408322849)
          ·
            refine ⟨837515195258605056242137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1116686927011473408322849 837515195258605056242137)
            ·
              refine ⟨628136396443953792181603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837515195258605056242137 628136396443953792181603)
              ·
                refine ⟨942204594665930688272405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628136396443953792181603 942204594665930688272405)
                ·
                  refine ⟨44165840374965501012769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 942204594665930688272405 44165840374965501012769)
                  ·
                    rfl

theorem cell23_774114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_774114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774114 prefixEnd_774114 := by exact prefixLift 774114
  have htrace : WordTrace (prefixWord ++ tailWord_774114) baseStart_774114 baseEnd_774114 := by
    simpa [prefixWord, tailWord_774114, baseEnd_774114] using wordTrace_append hprefix tailTrace_774114
  have hstable : (prefixWord ++ tailWord_774114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774114).length < 2 ^ (prefixWord ++ tailWord_774114).sum := by decide
  have hdescent : baseEnd_774114 < baseStart_774114 := by decide
  rcases family_descends (prefixWord ++ tailWord_774114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774134 : List Nat := [5, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2]
def baseStart_774134 : Nat := 118140960795 + 774134 * 2 ^ 59
def prefixEnd_774134 : Nat := 4983230072969 + 3 ^ 40 * 774134 * 2
def baseEnd_774134 : Nat := 397502832987779430864829

theorem tailTrace_774134 : CollatzResearch.WordTrace tailWord_774134 prefixEnd_774134 397502832987779430864829 := by
  unfold tailWord_774134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764686661090762775400591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18823324384968136270939637 1764686661090762775400591)
  ·
    refine ⟨2647029991636144163100887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764686661090762775400591 2647029991636144163100887)
    ·
      refine ⟨3970544987454216244651331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647029991636144163100887 3970544987454216244651331)
      ·
        refine ⟨5955817481181324366976997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970544987454216244651331 5955817481181324366976997)
        ·
          refine ⟨1116715777721498318808187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5955817481181324366976997 1116715777721498318808187)
          ·
            refine ⟨1675073666582247478212281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116715777721498318808187 1675073666582247478212281)
            ·
              refine ⟨1256305249936685608659211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675073666582247478212281 1256305249936685608659211)
              ·
                refine ⟨1884457874905028412988817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256305249936685608659211 1884457874905028412988817)
                ·
                  refine ⟨1413343406178771309741613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884457874905028412988817 1413343406178771309741613)
                  ·
                    refine ⟨530003777317039241153105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413343406178771309741613 530003777317039241153105)
                    ·
                      refine ⟨397502832987779430864829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530003777317039241153105 397502832987779430864829)
                      ·
                        rfl

theorem cell23_774134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_774134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774134 prefixEnd_774134 := by exact prefixLift 774134
  have htrace : WordTrace (prefixWord ++ tailWord_774134) baseStart_774134 baseEnd_774134 := by
    simpa [prefixWord, tailWord_774134, baseEnd_774134] using wordTrace_append hprefix tailTrace_774134
  have hstable : (prefixWord ++ tailWord_774134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774134).length < 2 ^ (prefixWord ++ tailWord_774134).sum := by decide
  have hdescent : baseEnd_774134 < baseStart_774134 := by decide
  rcases family_descends (prefixWord ++ tailWord_774134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774136 : List Nat := [2, 1, 2, 1, 1, 3, 4, 9]
def baseStart_774136 : Nat := 118140960795 + 774136 * 2 ^ 59
def prefixEnd_774136 : Nat := 4983230072969 + 3 ^ 40 * 774136 * 2
def baseEnd_774136 : Nat := 14722365183299571223697

theorem tailTrace_774136 : CollatzResearch.WordTrace tailWord_774136 prefixEnd_774136 14722365183299571223697 := by
  unfold tailWord_774136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14117529761722479373991131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18823373015629972498654841 14117529761722479373991131)
  ·
    refine ⟨21176294642583719060986697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14117529761722479373991131 21176294642583719060986697)
    ·
      refine ⟨15882220981937789295740023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21176294642583719060986697 15882220981937789295740023)
      ·
        refine ⟨23823331472906683943610035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15882220981937789295740023 23823331472906683943610035)
        ·
          refine ⟨35734997209360025915415053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23823331472906683943610035 35734997209360025915415053)
          ·
            refine ⟨13400623953510009718280645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35734997209360025915415053 13400623953510009718280645)
            ·
              refine ⟨2512616991283126822177621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13400623953510009718280645 2512616991283126822177621)
              ·
                refine ⟨14722365183299571223697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2512616991283126822177621 14722365183299571223697)
                ·
                  rfl

theorem cell23_774136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 9].length) (baseStart_774136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774136 prefixEnd_774136 := by exact prefixLift 774136
  have htrace : WordTrace (prefixWord ++ tailWord_774136) baseStart_774136 baseEnd_774136 := by
    simpa [prefixWord, tailWord_774136, baseEnd_774136] using wordTrace_append hprefix tailTrace_774136
  have hstable : (prefixWord ++ tailWord_774136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774136).length < 2 ^ (prefixWord ++ tailWord_774136).sum := by decide
  have hdescent : baseEnd_774136 < baseStart_774136 := by decide
  rcases family_descends (prefixWord ++ tailWord_774136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774201 : List Nat := [1, 2, 1, 5, 4, 1, 2, 1, 1, 2, 3]
def baseStart_774201 : Nat := 118140960795 + 774201 * 2 ^ 59
def prefixEnd_774201 : Nat := 4983230072969 + 3 ^ 40 * 774201 * 2
def baseEnd_774201 : Nat := 397537236191630668727021

theorem tailTrace_774201 : CollatzResearch.WordTrace tailWord_774201 prefixEnd_774201 397537236191630668727021 := by
  unfold tailWord_774201
  simp only [CollatzResearch.WordTrace]
  refine ⟨28237430268209474849098457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18824953512139649899398971 28237430268209474849098457)
  ·
    refine ⟨21178072701157106136823843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28237430268209474849098457 21178072701157106136823843)
    ·
      refine ⟨31767109051735659205235765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21178072701157106136823843 31767109051735659205235765)
      ·
        refine ⟨2978166473600218050490853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31767109051735659205235765 2978166473600218050490853)
        ·
          refine ⟨558406213800040884467035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2978166473600218050490853 558406213800040884467035)
          ·
            refine ⟨837609320700061326700553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558406213800040884467035 837609320700061326700553)
            ·
              refine ⟨628206990525045995025415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837609320700061326700553 628206990525045995025415)
              ·
                refine ⟨942310485787568992538123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628206990525045995025415 942310485787568992538123)
                ·
                  refine ⟨1413465728681353488807185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942310485787568992538123 1413465728681353488807185)
                  ·
                    refine ⟨1060099296511015116605389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1413465728681353488807185 1060099296511015116605389)
                    ·
                      refine ⟨397537236191630668727021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060099296511015116605389 397537236191630668727021)
                      ·
                        rfl

theorem cell23_774201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_774201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774201 prefixEnd_774201 := by exact prefixLift 774201
  have htrace : WordTrace (prefixWord ++ tailWord_774201) baseStart_774201 baseEnd_774201 := by
    simpa [prefixWord, tailWord_774201, baseEnd_774201] using wordTrace_append hprefix tailTrace_774201
  have hstable : (prefixWord ++ tailWord_774201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774201).length < 2 ^ (prefixWord ++ tailWord_774201).sum := by decide
  have hdescent : baseEnd_774201 < baseStart_774201 := by decide
  rcases family_descends (prefixWord ++ tailWord_774201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774214 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_774214 : Nat := 118140960795 + 774214 * 2 ^ 59
def prefixEnd_774214 : Nat := 4983230072969 + 3 ^ 40 * 774214 * 2
def baseEnd_774214 : Nat := 397543911440139117864461

theorem tailTrace_774214 : CollatzResearch.WordTrace tailWord_774214 prefixEnd_774214 397543911440139117864461 := by
  unfold tailWord_774214
  simp only [CollatzResearch.WordTrace]
  refine ⟨882434513036324314666303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18825269611441585379547797 882434513036324314666303)
  ·
    refine ⟨1323651769554486471999455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 882434513036324314666303 1323651769554486471999455)
    ·
      refine ⟨1985477654331729707999183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323651769554486471999455 1985477654331729707999183)
      ·
        refine ⟨2978216481497594561998775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985477654331729707999183 2978216481497594561998775)
        ·
          refine ⟨4467324722246391842998163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978216481497594561998775 4467324722246391842998163)
          ·
            refine ⟨6700987083369587764497245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467324722246391842998163 6700987083369587764497245)
            ·
              refine ⟨2512870156263595411686467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6700987083369587764497245 2512870156263595411686467)
              ·
                refine ⟨3769305234395393117529701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512870156263595411686467 3769305234395393117529701)
                ·
                  refine ⟨706744731449136209536819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3769305234395393117529701 706744731449136209536819)
                  ·
                    refine ⟨1060117097173704314305229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706744731449136209536819 1060117097173704314305229)
                    ·
                      refine ⟨397543911440139117864461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060117097173704314305229 397543911440139117864461)
                      ·
                        rfl

theorem cell23_774214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_774214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774214 prefixEnd_774214 := by exact prefixLift 774214
  have htrace : WordTrace (prefixWord ++ tailWord_774214) baseStart_774214 baseEnd_774214 := by
    simpa [prefixWord, tailWord_774214, baseEnd_774214] using wordTrace_append hprefix tailTrace_774214
  have hstable : (prefixWord ++ tailWord_774214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774214).length < 2 ^ (prefixWord ++ tailWord_774214).sum := by decide
  have hdescent : baseEnd_774214 < baseStart_774214 := by decide
  rcases family_descends (prefixWord ++ tailWord_774214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774220 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 3, 4, 2]
def baseStart_774220 : Nat := 118140960795 + 774220 * 2 ^ 59
def prefixEnd_774220 : Nat := 4983230072969 + 3 ^ 40 * 774220 * 2
def baseEnd_774220 : Nat := 397546992324066094389433

theorem tailTrace_774220 : CollatzResearch.WordTrace tailWord_774220 prefixEnd_774220 397546992324066094389433 := by
  unfold tailWord_774220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14119061627570320547020057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18825415503427094062693409 14119061627570320547020057)
  ·
    refine ⟨10589296220677740410265043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14119061627570320547020057 10589296220677740410265043)
    ·
      refine ⟨15883944331016610615397565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10589296220677740410265043 15883944331016610615397565)
      ·
        refine ⟨5956479124131228980774087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15883944331016610615397565 5956479124131228980774087)
        ·
          refine ⟨8934718686196843471161131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956479124131228980774087 8934718686196843471161131)
          ·
            refine ⟨13402078029295265206741697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934718686196843471161131 13402078029295265206741697)
            ·
              refine ⟨10051558521971448905056273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13402078029295265206741697 10051558521971448905056273)
              ·
                refine ⟨7538668891478586678792205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10051558521971448905056273 7538668891478586678792205)
                ·
                  refine ⟨2827000834304470004547077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7538668891478586678792205 2827000834304470004547077)
                  ·
                    refine ⟨530062656432088125852577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827000834304470004547077 530062656432088125852577)
                    ·
                      refine ⟨397546992324066094389433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530062656432088125852577 397546992324066094389433)
                      ·
                        rfl

theorem cell23_774220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_774220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774220 prefixEnd_774220 := by exact prefixLift 774220
  have htrace : WordTrace (prefixWord ++ tailWord_774220) baseStart_774220 baseEnd_774220 := by
    simpa [prefixWord, tailWord_774220, baseEnd_774220] using wordTrace_append hprefix tailTrace_774220
  have hstable : (prefixWord ++ tailWord_774220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774220).length < 2 ^ (prefixWord ++ tailWord_774220).sum := by decide
  have hdescent : baseEnd_774220 < baseStart_774220 := by decide
  rcases family_descends (prefixWord ++ tailWord_774220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774233 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 4]
def baseStart_774233 : Nat := 118140960795 + 774233 * 2 ^ 59
def prefixEnd_774233 : Nat := 4983230072969 + 3 ^ 40 * 774233 * 2
def baseEnd_774233 : Nat := 397553667572574543526873

theorem tailTrace_774233 : CollatzResearch.WordTrace tailWord_774233 prefixEnd_774233 397553667572574543526873 := by
  unfold tailWord_774233
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238597404093544314263353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18825731602729029542842235 28238597404093544314263353)
  ·
    refine ⟨21178948053070158235697515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28238597404093544314263353 21178948053070158235697515)
    ·
      refine ⟨31768422079605237353546273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21178948053070158235697515 31768422079605237353546273)
      ·
        refine ⟨23826316559703928015159705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31768422079605237353546273 23826316559703928015159705)
        ·
          refine ⟨17869737419777946011369779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23826316559703928015159705 17869737419777946011369779)
          ·
            refine ⟨26804606129666919017054669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17869737419777946011369779 26804606129666919017054669)
            ·
              refine ⟨10051727298625094631395501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26804606129666919017054669 10051727298625094631395501)
              ·
                refine ⟨3769397736984410486773313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10051727298625094631395501 3769397736984410486773313)
                ·
                  refine ⟨2827048302738307865079985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769397736984410486773313 2827048302738307865079985)
                  ·
                    refine ⟨2120286227053730898809989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2827048302738307865079985 2120286227053730898809989)
                    ·
                      refine ⟨397553667572574543526873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2120286227053730898809989 397553667572574543526873)
                      ·
                        rfl

theorem cell23_774233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_774233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774233 prefixEnd_774233 := by exact prefixLift 774233
  have htrace : WordTrace (prefixWord ++ tailWord_774233) baseStart_774233 baseEnd_774233 := by
    simpa [prefixWord, tailWord_774233, baseEnd_774233] using wordTrace_append hprefix tailTrace_774233
  have hstable : (prefixWord ++ tailWord_774233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774233).length < 2 ^ (prefixWord ++ tailWord_774233).sum := by decide
  have hdescent : baseEnd_774233 < baseStart_774233 := by decide
  rcases family_descends (prefixWord ++ tailWord_774233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774243 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 7]
def baseStart_774243 : Nat := 118140960795 + 774243 * 2 ^ 59
def prefixEnd_774243 : Nat := 4983230072969 + 3 ^ 40 * 774243 * 2
def baseEnd_774243 : Nat := 44173200264346611600203

theorem tailTrace_774243 : CollatzResearch.WordTrace tailWord_774243 prefixEnd_774243 44173200264346611600203 := by
  unfold tailWord_774243
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238962134057316022127383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18825974756038210681418255 28238962134057316022127383)
  ·
    refine ⟨42358443201085974033191075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28238962134057316022127383 42358443201085974033191075)
    ·
      refine ⟨63537664801628961049786613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42358443201085974033191075 63537664801628961049786613)
      ·
        refine ⟨5956656075152715098417495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63537664801628961049786613 5956656075152715098417495)
        ·
          refine ⟨8934984112729072647626243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956656075152715098417495 8934984112729072647626243)
          ·
            refine ⟨13402476169093608971439365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934984112729072647626243 13402476169093608971439365)
            ·
              refine ⟨2512964281705051682144881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13402476169093608971439365 2512964281705051682144881)
              ·
                refine ⟨1884723211278788761608661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512964281705051682144881 1884723211278788761608661)
                ·
                  refine ⟨44173200264346611600203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1884723211278788761608661 44173200264346611600203)
                  ·
                    rfl

theorem cell23_774243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 7].length) (baseStart_774243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774243 prefixEnd_774243 := by exact prefixLift 774243
  have htrace : WordTrace (prefixWord ++ tailWord_774243) baseStart_774243 baseEnd_774243 := by
    simpa [prefixWord, tailWord_774243, baseEnd_774243] using wordTrace_append hprefix tailTrace_774243
  have hstable : (prefixWord ++ tailWord_774243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774243).length < 2 ^ (prefixWord ++ tailWord_774243).sum := by decide
  have hdescent : baseEnd_774243 < baseStart_774243 := by decide
  rcases family_descends (prefixWord ++ tailWord_774243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774290 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_774290 : Nat := 118140960795 + 774290 * 2 ^ 59
def prefixEnd_774290 : Nat := 4983230072969 + 3 ^ 40 * 774290 * 2
def baseEnd_774290 : Nat := 132527645323293606838037

theorem tailTrace_774290 : CollatzResearch.WordTrace tailWord_774290 prefixEnd_774290 132527645323293606838037 := by
  unfold tailWord_774290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7060169091221760762272081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18827117576591362032725549 7060169091221760762272081)
  ·
    refine ⟨5295126818416320571704061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7060169091221760762272081 5295126818416320571704061)
    ·
      refine ⟨1985672556906120214389023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5295126818416320571704061 1985672556906120214389023)
      ·
        refine ⟨2978508835359180321583535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1985672556906120214389023 2978508835359180321583535)
        ·
          refine ⟨4467763253038770482375303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978508835359180321583535 4467763253038770482375303)
          ·
            refine ⟨6701644879558155723562955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467763253038770482375303 6701644879558155723562955)
            ·
              refine ⟨10052467319337233585344433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6701644879558155723562955 10052467319337233585344433)
              ·
                refine ⟨7539350489502925189008325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10052467319337233585344433 7539350489502925189008325)
                ·
                  refine ⟨1413628216781798472939061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7539350489502925189008325 1413628216781798472939061)
                  ·
                    refine ⟨132527645323293606838037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1413628216781798472939061 132527645323293606838037)
                    ·
                      rfl

theorem cell23_774290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_774290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774290 prefixEnd_774290 := by exact prefixLift 774290
  have htrace : WordTrace (prefixWord ++ tailWord_774290) baseStart_774290 baseEnd_774290 := by
    simpa [prefixWord, tailWord_774290, baseEnd_774290] using wordTrace_append hprefix tailTrace_774290
  have hstable : (prefixWord ++ tailWord_774290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774290).length < 2 ^ (prefixWord ++ tailWord_774290).sum := by decide
  have hdescent : baseEnd_774290 < baseStart_774290 := by decide
  rcases family_descends (prefixWord ++ tailWord_774290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774323 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_774323 : Nat := 118140960795 + 774323 * 2 ^ 59
def prefixEnd_774323 : Nat := 4983230072969 + 3 ^ 40 * 774323 * 2
def baseEnd_774323 : Nat := 397599880831479191401459

theorem tailTrace_774323 : CollatzResearch.WordTrace tailWord_774323 prefixEnd_774323 397599880831479191401459 := by
  unfold tailWord_774323
  simp only [CollatzResearch.WordTrace]
  refine ⟨28241879973767489685039623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18827919982511659790026415 28241879973767489685039623)
  ·
    refine ⟨42362819960651234527559435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28241879973767489685039623 42362819960651234527559435)
    ·
      refine ⟨63544229940976851791339153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42362819960651234527559435 63544229940976851791339153)
      ·
        refine ⟨47658172455732638843504365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63544229940976851791339153 47658172455732638843504365)
        ·
          refine ⟨17871814670899739566314137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47658172455732638843504365 17871814670899739566314137)
          ·
            refine ⟨13403861003174804674735603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17871814670899739566314137 13403861003174804674735603)
            ·
              refine ⟨20105791504762207012103405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13403861003174804674735603 20105791504762207012103405)
              ·
                refine ⟨7539671814285827629538777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20105791504762207012103405 7539671814285827629538777)
                ·
                  refine ⟨5654753860714370722154083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7539671814285827629538777 5654753860714370722154083)
                  ·
                    refine ⟨8482130791071556083231125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5654753860714370722154083 8482130791071556083231125)
                    ·
                      refine ⟨397599880831479191401459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8482130791071556083231125 397599880831479191401459)
                      ·
                        rfl

theorem cell23_774323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_774323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774323 prefixEnd_774323 := by exact prefixLift 774323
  have htrace : WordTrace (prefixWord ++ tailWord_774323) baseStart_774323 baseEnd_774323 := by
    simpa [prefixWord, tailWord_774323, baseEnd_774323] using wordTrace_append hprefix tailTrace_774323
  have hstable : (prefixWord ++ tailWord_774323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774323).length < 2 ^ (prefixWord ++ tailWord_774323).sum := by decide
  have hdescent : baseEnd_774323 < baseStart_774323 := by decide
  rcases family_descends (prefixWord ++ tailWord_774323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774387 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 4, 3, 2]
def baseStart_774387 : Nat := 118140960795 + 774387 * 2 ^ 59
def prefixEnd_774387 : Nat := 4983230072969 + 3 ^ 40 * 774387 * 2
def baseEnd_774387 : Nat := 397632743593366941001165

theorem tailTrace_774387 : CollatzResearch.WordTrace tailWord_774387 prefixEnd_774387 397632743593366941001165 := by
  unfold tailWord_774387
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244214245535628615369415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18829476163690419076912943 28244214245535628615369415)
  ·
    refine ⟨42366321368303442923054123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28244214245535628615369415 42366321368303442923054123)
    ·
      refine ⟨63549482052455164384581185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42366321368303442923054123 63549482052455164384581185)
      ·
        refine ⟨47662111539341373288435889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63549482052455164384581185 47662111539341373288435889)
        ·
          refine ⟨35746583654506029966326917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47662111539341373288435889 35746583654506029966326917)
          ·
            refine ⟨6702484435219880618686297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35746583654506029966326917 6702484435219880618686297)
            ·
              refine ⟨5026863326414910464014723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6702484435219880618686297 5026863326414910464014723)
              ·
                refine ⟨7540294989622365696022085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026863326414910464014723 7540294989622365696022085)
                ·
                  refine ⟨1413805310554193568004141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7540294989622365696022085 1413805310554193568004141)
                  ·
                    refine ⟨530176991457822588001553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413805310554193568004141 530176991457822588001553)
                    ·
                      refine ⟨397632743593366941001165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530176991457822588001553 397632743593366941001165)
                      ·
                        rfl

theorem cell23_774387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3, 2].length) (baseStart_774387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774387 prefixEnd_774387 := by exact prefixLift 774387
  have htrace : WordTrace (prefixWord ++ tailWord_774387) baseStart_774387 baseEnd_774387 := by
    simpa [prefixWord, tailWord_774387, baseEnd_774387] using wordTrace_append hprefix tailTrace_774387
  have hstable : (prefixWord ++ tailWord_774387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774387).length < 2 ^ (prefixWord ++ tailWord_774387).sum := by decide
  have hdescent : baseEnd_774387 < baseStart_774387 := by decide
  rcases family_descends (prefixWord ++ tailWord_774387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774394 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_774394 : Nat := 118140960795 + 774394 * 2 ^ 59
def prefixEnd_774394 : Nat := 4983230072969 + 3 ^ 40 * 774394 * 2
def baseEnd_774394 : Nat := 397636337957948413613633

theorem tailTrace_774394 : CollatzResearch.WordTrace tailWord_774394 prefixEnd_774394 397636337957948413613633 := by
  unfold tailWord_774394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061117389127567202718559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18829646371006845873916157 7061117389127567202718559)
  ·
    refine ⟨10591676083691350804077839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7061117389127567202718559 10591676083691350804077839)
    ·
      refine ⟨15887514125537026206116759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591676083691350804077839 15887514125537026206116759)
      ·
        refine ⟨23831271188305539309175139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887514125537026206116759 23831271188305539309175139)
        ·
          refine ⟨35746906782458308963762709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831271188305539309175139 35746906782458308963762709)
          ·
            refine ⟨1675636255427733232676377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35746906782458308963762709 1675636255427733232676377)
            ·
              refine ⟨1256727191570799924507283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675636255427733232676377 1256727191570799924507283)
              ·
                refine ⟨1885090787356199886760925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256727191570799924507283 1885090787356199886760925)
                ·
                  refine ⟨706909045258574957535347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1885090787356199886760925 706909045258574957535347)
                  ·
                    refine ⟨1060363567887862436303021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706909045258574957535347 1060363567887862436303021)
                    ·
                      refine ⟨397636337957948413613633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060363567887862436303021 397636337957948413613633)
                      ·
                        rfl

theorem cell23_774394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_774394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774394 prefixEnd_774394 := by exact prefixLift 774394
  have htrace : WordTrace (prefixWord ++ tailWord_774394) baseStart_774394 baseEnd_774394 := by
    simpa [prefixWord, tailWord_774394, baseEnd_774394] using wordTrace_append hprefix tailTrace_774394
  have hstable : (prefixWord ++ tailWord_774394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774394).length < 2 ^ (prefixWord ++ tailWord_774394).sum := by decide
  have hdescent : baseEnd_774394 < baseStart_774394 := by decide
  rcases family_descends (prefixWord ++ tailWord_774394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774400 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_774400 : Nat := 118140960795 + 774400 * 2 ^ 59
def prefixEnd_774400 : Nat := 4983230072969 + 3 ^ 40 * 774400 * 2
def baseEnd_774400 : Nat := 397639418841875390138605

theorem tailTrace_774400 : CollatzResearch.WordTrace tailWord_774400 prefixEnd_774400 397639418841875390138605 := by
  unfold tailWord_774400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14122344197244265917796327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18829792262992354557061769 14122344197244265917796327)
  ·
    refine ⟨21183516295866398876694491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14122344197244265917796327 21183516295866398876694491)
    ·
      refine ⟨31775274443799598315041737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21183516295866398876694491 31775274443799598315041737)
      ·
        refine ⟨23831455832849698736281303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31775274443799598315041737 23831455832849698736281303)
        ·
          refine ⟨35747183749274548104421955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831455832849698736281303 35747183749274548104421955)
          ·
            refine ⟨53620775623911822156632933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35747183749274548104421955 53620775623911822156632933)
            ·
              refine ⟨10053895429483466654368675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53620775623911822156632933 10053895429483466654368675)
              ·
                refine ⟨15080843144225199981553013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10053895429483466654368675 15080843144225199981553013)
                ·
                  refine ⟨1413829044771112498270595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15080843144225199981553013 1413829044771112498270595)
                  ·
                    refine ⟨2120743567156668747405893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1413829044771112498270595 2120743567156668747405893)
                    ·
                      refine ⟨397639418841875390138605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2120743567156668747405893 397639418841875390138605)
                      ·
                        rfl

theorem cell23_774400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_774400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774400 prefixEnd_774400 := by exact prefixLift 774400
  have htrace : WordTrace (prefixWord ++ tailWord_774400) baseStart_774400 baseEnd_774400 := by
    simpa [prefixWord, tailWord_774400, baseEnd_774400] using wordTrace_append hprefix tailTrace_774400
  have hstable : (prefixWord ++ tailWord_774400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774400).length < 2 ^ (prefixWord ++ tailWord_774400).sum := by decide
  have hdescent : baseEnd_774400 < baseStart_774400 := by decide
  rcases family_descends (prefixWord ++ tailWord_774400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774417 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 4]
def baseStart_774417 : Nat := 118140960795 + 774417 * 2 ^ 59
def prefixEnd_774417 : Nat := 4983230072969 + 3 ^ 40 * 774417 * 2
def baseEnd_774417 : Nat := 397648148013001823626027

theorem tailTrace_774417 : CollatzResearch.WordTrace tailWord_774417 prefixEnd_774417 397648148013001823626027 := by
  unfold tailWord_774417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28245308435426943738961505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18830205623617962492641003 28245308435426943738961505)
  ·
    refine ⟨21183981326570207804221129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28245308435426943738961505 21183981326570207804221129)
    ·
      refine ⟨15887985994927655853165847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21183981326570207804221129 15887985994927655853165847)
      ·
        refine ⟨23831978992391483779748771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15887985994927655853165847 23831978992391483779748771)
        ·
          refine ⟨35747968488587225669623157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23831978992391483779748771 35747968488587225669623157)
          ·
            refine ⟨3351372045805052406527171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35747968488587225669623157 3351372045805052406527171)
            ·
              refine ⟨5027058068707578609790757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351372045805052406527171 5027058068707578609790757)
              ·
                refine ⟨942573387882670989335767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5027058068707578609790757 942573387882670989335767)
                ·
                  refine ⟨1413860081824006484003651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942573387882670989335767 1413860081824006484003651)
                  ·
                    refine ⟨2120790122736009726005477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1413860081824006484003651 2120790122736009726005477)
                    ·
                      refine ⟨397648148013001823626027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2120790122736009726005477 397648148013001823626027)
                      ·
                        rfl

theorem cell23_774417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_774417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774417 prefixEnd_774417 := by exact prefixLift 774417
  have htrace : WordTrace (prefixWord ++ tailWord_774417) baseStart_774417 baseEnd_774417 := by
    simpa [prefixWord, tailWord_774417, baseEnd_774417] using wordTrace_append hprefix tailTrace_774417
  have hstable : (prefixWord ++ tailWord_774417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774417).length < 2 ^ (prefixWord ++ tailWord_774417).sum := by decide
  have hdescent : baseEnd_774417 < baseStart_774417 := by decide
  rcases family_descends (prefixWord ++ tailWord_774417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774434 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_774434 : Nat := 118140960795 + 774434 * 2 ^ 59
def prefixEnd_774434 : Nat := 4983230072969 + 3 ^ 40 * 774434 * 2
def baseEnd_774434 : Nat := 397656877184128257113449

theorem tailTrace_774434 : CollatzResearch.WordTrace tailWord_774434 prefixEnd_774434 397656877184128257113449 := by
  unfold tailWord_774434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7061482119091338910582589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18830618984243570428220237 7061482119091338910582589)
  ·
    refine ⟨2648055794659252091468471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7061482119091338910582589 2648055794659252091468471)
    ·
      refine ⟨3972083691988878137202707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648055794659252091468471 3972083691988878137202707)
      ·
        refine ⟨5958125537983317205804061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972083691988878137202707 5958125537983317205804061)
        ·
          refine ⟨2234297076743743952176523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5958125537983317205804061 2234297076743743952176523)
          ·
            refine ⟨3351445615115615928264785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234297076743743952176523 3351445615115615928264785)
            ·
              refine ⟨2513584211336711946198589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3351445615115615928264785 2513584211336711946198589)
              ·
                refine ⟨942594079251266979824471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2513584211336711946198589 942594079251266979824471)
                ·
                  refine ⟨1413891118876900469736707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942594079251266979824471 1413891118876900469736707)
                  ·
                    refine ⟨2120836678315350704605061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1413891118876900469736707 2120836678315350704605061)
                    ·
                      refine ⟨397656877184128257113449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2120836678315350704605061 397656877184128257113449)
                      ·
                        rfl

theorem cell23_774434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_774434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774434 prefixEnd_774434 := by exact prefixLift 774434
  have htrace : WordTrace (prefixWord ++ tailWord_774434) baseStart_774434 baseEnd_774434 := by
    simpa [prefixWord, tailWord_774434, baseEnd_774434] using wordTrace_append hprefix tailTrace_774434
  have hstable : (prefixWord ++ tailWord_774434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774434).length < 2 ^ (prefixWord ++ tailWord_774434).sum := by decide
  have hdescent : baseEnd_774434 < baseStart_774434 := by decide
  rcases family_descends (prefixWord ++ tailWord_774434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774445 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_774445 : Nat := 118140960795 + 774445 * 2 ^ 59
def prefixEnd_774445 : Nat := 4983230072969 + 3 ^ 40 * 774445 * 2
def baseEnd_774445 : Nat := 397662525471327714075899

theorem tailTrace_774445 : CollatzResearch.WordTrace tailWord_774445 prefixEnd_774445 397662525471327714075899 := by
  unfold tailWord_774445
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246329679325504520980789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18830886452883669680653859 28246329679325504520980789)
  ·
    refine ⟨2648093407436766048841949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28246329679325504520980789 2648093407436766048841949)
    ·
      refine ⟨993035027788787268315731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2648093407436766048841949 993035027788787268315731)
      ·
        refine ⟨1489552541683180902473597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993035027788787268315731 1489552541683180902473597)
        ·
          refine ⟨558582203131192838427599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489552541683180902473597 558582203131192838427599)
          ·
            refine ⟨837873304696789257641399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558582203131192838427599 837873304696789257641399)
            ·
              refine ⟨1256809957045183886462099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837873304696789257641399 1256809957045183886462099)
              ·
                refine ⟨1885214935567775829693149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256809957045183886462099 1885214935567775829693149)
                ·
                  refine ⟨706955600837915936134931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1885214935567775829693149 706955600837915936134931)
                  ·
                    refine ⟨1060433401256873904202397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 706955600837915936134931 1060433401256873904202397)
                    ·
                      refine ⟨397662525471327714075899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060433401256873904202397 397662525471327714075899)
                      ·
                        rfl

theorem cell23_774445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_774445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774445 prefixEnd_774445 := by exact prefixLift 774445
  have htrace : WordTrace (prefixWord ++ tailWord_774445) baseStart_774445 baseEnd_774445 := by
    simpa [prefixWord, tailWord_774445, baseEnd_774445] using wordTrace_append hprefix tailTrace_774445
  have hstable : (prefixWord ++ tailWord_774445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774445).length < 2 ^ (prefixWord ++ tailWord_774445).sum := by decide
  have hdescent : baseEnd_774445 < baseStart_774445 := by decide
  rcases family_descends (prefixWord ++ tailWord_774445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774457 : List Nat := [1, 2, 1, 6, 1, 2, 2, 8]
def baseStart_774457 : Nat := 118140960795 + 774457 * 2 ^ 59
def prefixEnd_774457 : Nat := 4983230072969 + 3 ^ 40 * 774457 * 2
def baseEnd_774457 : Nat := 14728469897747469152809

theorem tailTrace_774457 : CollatzResearch.WordTrace tailWord_774457 prefixEnd_774457 14728469897747469152809 := by
  unfold tailWord_774457
  simp only [CollatzResearch.WordTrace]
  refine ⟨28246767355282030570417625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18831178236854687046945083 28246767355282030570417625)
  ·
    refine ⟨21185075516461522927813219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28246767355282030570417625 21185075516461522927813219)
    ·
      refine ⟨31777613274692284391719829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21185075516461522927813219 31777613274692284391719829)
      ·
        refine ⟨1489575622251200830861867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31777613274692284391719829 1489575622251200830861867)
        ·
          refine ⟨2234363433376801246292801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489575622251200830861867 2234363433376801246292801)
          ·
            refine ⟨1675772575032600934719601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2234363433376801246292801 1675772575032600934719601)
            ·
              refine ⟨1256829431274450701039701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675772575032600934719601 1256829431274450701039701)
              ·
                refine ⟨14728469897747469152809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1256829431274450701039701 14728469897747469152809)
                ·
                  rfl

theorem cell23_774457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 8].length) (baseStart_774457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774457 prefixEnd_774457 := by exact prefixLift 774457
  have htrace : WordTrace (prefixWord ++ tailWord_774457) baseStart_774457 baseEnd_774457 := by
    simpa [prefixWord, tailWord_774457, baseEnd_774457] using wordTrace_append hprefix tailTrace_774457
  have hstable : (prefixWord ++ tailWord_774457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774457).length < 2 ^ (prefixWord ++ tailWord_774457).sum := by decide
  have hdescent : baseEnd_774457 < baseStart_774457 := by decide
  rcases family_descends (prefixWord ++ tailWord_774457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774460 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_774460 : Nat := 118140960795 + 774460 * 2 ^ 59
def prefixEnd_774460 : Nat := 4983230072969 + 3 ^ 40 * 774460 * 2
def baseEnd_774460 : Nat := 397670227681145155388329

theorem tailTrace_774460 : CollatzResearch.WordTrace tailWord_774460 prefixEnd_774460 397670227681145155388329 := by
  unfold tailWord_774460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123438387135581041388417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18831251182847441388517889 14123438387135581041388417)
  ·
    refine ⟨10592578790351685781041313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14123438387135581041388417 10592578790351685781041313)
    ·
      refine ⟨7944434092763764335780985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10592578790351685781041313 7944434092763764335780985)
      ·
        refine ⟨5958325569572823251835739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7944434092763764335780985 5958325569572823251835739)
        ·
          refine ⟨8937488354359234877753609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958325569572823251835739 8937488354359234877753609)
          ·
            refine ⟨6703116265769426158315207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8937488354359234877753609 6703116265769426158315207)
            ·
              refine ⟨10054674398654139237472811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703116265769426158315207 10054674398654139237472811)
              ·
                refine ⟨15082011597981208856209217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10054674398654139237472811 15082011597981208856209217)
                ·
                  refine ⟨11311508698485906642156913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15082011597981208856209217 11311508698485906642156913)
                  ·
                    refine ⟨8483631523864429981617685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11311508698485906642156913 8483631523864429981617685)
                    ·
                      refine ⟨397670227681145155388329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8483631523864429981617685 397670227681145155388329)
                      ·
                        rfl

theorem cell23_774460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_774460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774460 prefixEnd_774460 := by exact prefixLift 774460
  have htrace : WordTrace (prefixWord ++ tailWord_774460) baseStart_774460 baseEnd_774460 := by
    simpa [prefixWord, tailWord_774460, baseEnd_774460] using wordTrace_append hprefix tailTrace_774460
  have hstable : (prefixWord ++ tailWord_774460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774460).length < 2 ^ (prefixWord ++ tailWord_774460).sum := by decide
  have hdescent : baseEnd_774460 < baseStart_774460 := by decide
  rcases family_descends (prefixWord ++ tailWord_774460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774468 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_774468 : Nat := 118140960795 + 774468 * 2 ^ 59
def prefixEnd_774468 : Nat := 4983230072969 + 3 ^ 40 * 774468 * 2
def baseEnd_774468 : Nat := 397674335526381124088293

theorem tailTrace_774468 : CollatzResearch.WordTrace tailWord_774468 prefixEnd_774468 397674335526381124088293 := by
  unfold tailWord_774468
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123584279121089724534029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18831445705494786299378705 14123584279121089724534029)
  ·
    refine ⟨5296344104670408646700261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14123584279121089724534029 5296344104670408646700261)
    ·
      refine ⟨993064519625701621256299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5296344104670408646700261 993064519625701621256299)
      ·
        refine ⟨1489596779438552431884449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993064519625701621256299 1489596779438552431884449)
        ·
          refine ⟨1117197584578914323913337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489596779438552431884449 1117197584578914323913337)
          ·
            refine ⟨837898188434185742935003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117197584578914323913337 837898188434185742935003)
            ·
              refine ⟨1256847282651278614402505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 837898188434185742935003 1256847282651278614402505)
              ·
                refine ⟨942635461988458960801879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256847282651278614402505 942635461988458960801879)
                ·
                  refine ⟨1413953192982688441202819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942635461988458960801879 1413953192982688441202819)
                  ·
                    refine ⟨2120929789474032661804229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1413953192982688441202819 2120929789474032661804229)
                    ·
                      refine ⟨397674335526381124088293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2120929789474032661804229 397674335526381124088293)
                      ·
                        rfl

theorem cell23_774468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_774468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774468 prefixEnd_774468 := by exact prefixLift 774468
  have htrace : WordTrace (prefixWord ++ tailWord_774468) baseStart_774468 baseEnd_774468 := by
    simpa [prefixWord, tailWord_774468, baseEnd_774468] using wordTrace_append hprefix tailTrace_774468
  have hstable : (prefixWord ++ tailWord_774468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774468).length < 2 ^ (prefixWord ++ tailWord_774468).sum := by decide
  have hdescent : baseEnd_774468 < baseStart_774468 := by decide
  rcases family_descends (prefixWord ++ tailWord_774468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774484 : List Nat := [2, 4, 1, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_774484 : Nat := 118140960795 + 774484 * 2 ^ 59
def prefixEnd_774484 : Nat := 4983230072969 + 3 ^ 40 * 774484 * 2
def baseEnd_774484 : Nat := 397682551216853061488219

theorem tailTrace_774484 : CollatzResearch.WordTrace tailWord_774484 prefixEnd_774484 397682551216853061488219 := by
  unfold tailWord_774484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123876063092107090825253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18831834750789476121100337 14123876063092107090825253)
  ·
    refine ⟨2648226761829770079529735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14123876063092107090825253 2648226761829770079529735)
    ·
      refine ⟨3972340142744655119294603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648226761829770079529735 3972340142744655119294603)
      ·
        refine ⟨5958510214116982678941905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3972340142744655119294603 5958510214116982678941905)
        ·
          refine ⟨4468882660587737009206429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5958510214116982678941905 4468882660587737009206429)
          ·
            refine ⟨1675830997720401378452411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4468882660587737009206429 1675830997720401378452411)
            ·
              refine ⟨2513746496580602067678617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675830997720401378452411 2513746496580602067678617)
              ·
                refine ⟨1885309872435451550758963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513746496580602067678617 1885309872435451550758963)
                ·
                  refine ⟨2827964808653177326138445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885309872435451550758963 2827964808653177326138445)
                  ·
                    refine ⟨1060486803244941497301917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2827964808653177326138445 1060486803244941497301917)
                    ·
                      refine ⟨397682551216853061488219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060486803244941497301917 397682551216853061488219)
                      ·
                        rfl

theorem cell23_774484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_774484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774484 prefixEnd_774484 := by exact prefixLift 774484
  have htrace : WordTrace (prefixWord ++ tailWord_774484) baseStart_774484 baseEnd_774484 := by
    simpa [prefixWord, tailWord_774484, baseEnd_774484] using wordTrace_append hprefix tailTrace_774484
  have hstable : (prefixWord ++ tailWord_774484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774484).length < 2 ^ (prefixWord ++ tailWord_774484).sum := by decide
  have hdescent : baseEnd_774484 < baseStart_774484 := by decide
  rcases family_descends (prefixWord ++ tailWord_774484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774501 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_774501 : Nat := 118140960795 + 774501 * 2 ^ 59
def prefixEnd_774501 : Nat := 4983230072969 + 3 ^ 40 * 774501 * 2
def baseEnd_774501 : Nat := 397691280387979494975641

theorem tailTrace_774501 : CollatzResearch.WordTrace tailWord_774501 prefixEnd_774501 397691280387979494975641 := by
  unfold tailWord_774501
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248372167122626085019357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18832248111415084056679571 28248372167122626085019357)
  ·
    refine ⟨10593139562670984781882259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28248372167122626085019357 10593139562670984781882259)
    ·
      refine ⟨15889709344006477172823389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10593139562670984781882259 15889709344006477172823389)
      ·
        refine ⟨5958641004002428939808771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15889709344006477172823389 5958641004002428939808771)
        ·
          refine ⟨8937961506003643409713157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958641004002428939808771 8937961506003643409713157)
          ·
            refine ⟨1675867782375683139321217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8937961506003643409713157 1675867782375683139321217)
            ·
              refine ⟨1256900836781762354490913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675867782375683139321217 1256900836781762354490913)
              ·
                refine ⟨942675627586321765868185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256900836781762354490913 942675627586321765868185)
                ·
                  refine ⟨707006720689741324401139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942675627586321765868185 707006720689741324401139)
                  ·
                    refine ⟨1060510081034611986601709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707006720689741324401139 1060510081034611986601709)
                    ·
                      refine ⟨397691280387979494975641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060510081034611986601709 397691280387979494975641)
                      ·
                        rfl

theorem cell23_774501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_774501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774501 prefixEnd_774501 := by exact prefixLift 774501
  have htrace : WordTrace (prefixWord ++ tailWord_774501) baseStart_774501 baseEnd_774501 := by
    simpa [prefixWord, tailWord_774501, baseEnd_774501] using wordTrace_append hprefix tailTrace_774501
  have hstable : (prefixWord ++ tailWord_774501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774501).length < 2 ^ (prefixWord ++ tailWord_774501).sum := by decide
  have hdescent : baseEnd_774501 < baseStart_774501 := by decide
  rcases family_descends (prefixWord ++ tailWord_774501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774517 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_774517 : Nat := 118140960795 + 774517 * 2 ^ 59
def prefixEnd_774517 : Nat := 4983230072969 + 3 ^ 40 * 774517 * 2
def baseEnd_774517 : Nat := 132566498692817144125189

theorem tailTrace_774517 : CollatzResearch.WordTrace tailWord_774517 prefixEnd_774517 132566498692817144125189 := by
  unfold tailWord_774517
  simp only [CollatzResearch.WordTrace]
  refine ⟨28248955735064660817601805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18832637156709773878401203 28248955735064660817601805)
  ·
    refine ⟨10593358400649247806600677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28248955735064660817601805 10593358400649247806600677)
    ·
      refine ⟨1986254700121733963737627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10593358400649247806600677 1986254700121733963737627)
      ·
        refine ⟨2979382050182600945606441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986254700121733963737627 2979382050182600945606441)
        ·
          refine ⟨2234536537636950709204831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2979382050182600945606441 2234536537636950709204831)
          ·
            refine ⟨3351804806455426063807247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234536537636950709204831 3351804806455426063807247)
            ·
              refine ⟨5027707209683139095710871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351804806455426063807247 5027707209683139095710871)
              ·
                refine ⟨7541560814524708643566307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027707209683139095710871 7541560814524708643566307)
                ·
                  refine ⟨11312341221787062965349461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7541560814524708643566307 11312341221787062965349461)
                  ·
                    refine ⟨132566498692817144125189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11312341221787062965349461 132566498692817144125189)
                    ·
                      rfl

theorem cell23_774517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_774517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774517 prefixEnd_774517 := by exact prefixLift 774517
  have htrace : WordTrace (prefixWord ++ tailWord_774517) baseStart_774517 baseEnd_774517 := by
    simpa [prefixWord, tailWord_774517, baseEnd_774517] using wordTrace_append hprefix tailTrace_774517
  have hstable : (prefixWord ++ tailWord_774517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774517).length < 2 ^ (prefixWord ++ tailWord_774517).sum := by decide
  have hdescent : baseEnd_774517 < baseStart_774517 := by decide
  rcases family_descends (prefixWord ++ tailWord_774517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774518 : List Nat := [5, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3]
def baseStart_774518 : Nat := 118140960795 + 774518 * 2 ^ 59
def prefixEnd_774518 : Nat := 4983230072969 + 3 ^ 40 * 774518 * 2
def baseEnd_774518 : Nat := 397700009559105928463063

theorem tailTrace_774518 : CollatzResearch.WordTrace tailWord_774518 prefixEnd_774518 397700009559105928463063 := by
  unfold tailWord_774518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765562013003814874274263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18832661472040691992258805 1765562013003814874274263)
  ·
    refine ⟨2648343019505722311411395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1765562013003814874274263 2648343019505722311411395)
    ·
      refine ⟨3972514529258583467117093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648343019505722311411395 3972514529258583467117093)
      ·
        refine ⟨744846474235984400084455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3972514529258583467117093 744846474235984400084455)
        ·
          refine ⟨1117269711353976600126683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744846474235984400084455 1117269711353976600126683)
          ·
            refine ⟨1675904567030964900190025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117269711353976600126683 1675904567030964900190025)
            ·
              refine ⟨1256928425273223675142519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675904567030964900190025 1256928425273223675142519)
              ·
                refine ⟨1885392637909835512713779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1256928425273223675142519 1885392637909835512713779)
                ·
                  refine ⟨2828088956864753269070669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885392637909835512713779 2828088956864753269070669)
                  ·
                    refine ⟨1060533358824282475901501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2828088956864753269070669 1060533358824282475901501)
                    ·
                      refine ⟨397700009559105928463063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060533358824282475901501 397700009559105928463063)
                      ·
                        rfl

theorem cell23_774518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_774518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774518 prefixEnd_774518 := by exact prefixLift 774518
  have htrace : WordTrace (prefixWord ++ tailWord_774518) baseStart_774518 baseEnd_774518 := by
    simpa [prefixWord, tailWord_774518, baseEnd_774518] using wordTrace_append hprefix tailTrace_774518
  have hstable : (prefixWord ++ tailWord_774518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774518).length < 2 ^ (prefixWord ++ tailWord_774518).sum := by decide
  have hdescent : baseEnd_774518 < baseStart_774518 := by decide
  rcases family_descends (prefixWord ++ tailWord_774518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774564 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 5]
def baseStart_774564 : Nat := 118140960795 + 774564 * 2 ^ 59
def prefixEnd_774564 : Nat := 4983230072969 + 3 ^ 40 * 774564 * 2
def baseEnd_774564 : Nat := 44191514407690305387539

theorem tailTrace_774564 : CollatzResearch.WordTrace tailWord_774564 prefixEnd_774564 44191514407690305387539 := by
  unfold tailWord_774564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125334982947193922281373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18833779977262925229708497 14125334982947193922281373)
  ·
    refine ⟨5297000618605197720855515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14125334982947193922281373 5297000618605197720855515)
    ·
      refine ⟨7945500927907796581283273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297000618605197720855515 7945500927907796581283273)
      ·
        refine ⟨5959125695930847435962455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945500927907796581283273 5959125695930847435962455)
        ·
          refine ⟨8938688543896271153943683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5959125695930847435962455 8938688543896271153943683)
          ·
            refine ⟨13408032815844406730915525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938688543896271153943683 13408032815844406730915525)
            ·
              refine ⟨2514006152970826262046661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13408032815844406730915525 2514006152970826262046661)
              ·
                refine ⟨471376153682029924133749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2514006152970826262046661 471376153682029924133749)
                ·
                  refine ⟨44191514407690305387539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471376153682029924133749 44191514407690305387539)
                  ·
                    rfl

theorem cell23_774564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_774564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774564 prefixEnd_774564 := by exact prefixLift 774564
  have htrace : WordTrace (prefixWord ++ tailWord_774564) baseStart_774564 baseEnd_774564 := by
    simpa [prefixWord, tailWord_774564, baseEnd_774564] using wordTrace_append hprefix tailTrace_774564
  have hstable : (prefixWord ++ tailWord_774564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774564).length < 2 ^ (prefixWord ++ tailWord_774564).sum := by decide
  have hdescent : baseEnd_774564 < baseStart_774564 := by decide
  rcases family_descends (prefixWord ++ tailWord_774564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774577 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 7]
def baseStart_774577 : Nat := 118140960795 + 774577 * 2 ^ 59
def prefixEnd_774577 : Nat := 4983230072969 + 3 ^ 40 * 774577 * 2
def baseEnd_774577 : Nat := 132576768305907065875097

theorem tailTrace_774577 : CollatzResearch.WordTrace tailWord_774577 prefixEnd_774577 132576768305907065875097 := by
  unfold tailWord_774577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251144114847291064785985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18834096076564860709857323 28251144114847291064785985)
  ·
    refine ⟨21188358086135468298589489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28251144114847291064785985 21188358086135468298589489)
    ·
      refine ⟨15891268564601601223942117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21188358086135468298589489 15891268564601601223942117)
      ·
        refine ⟨2979612855862800229489147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15891268564601601223942117 2979612855862800229489147)
        ·
          refine ⟨4469419283794200344233721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979612855862800229489147 4469419283794200344233721)
          ·
            refine ⟨3352064462845650258175291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4469419283794200344233721 3352064462845650258175291)
            ·
              refine ⟨5028096694268475387262937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352064462845650258175291 5028096694268475387262937)
              ·
                refine ⟨3771072520701356540447203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028096694268475387262937 3771072520701356540447203)
                ·
                  refine ⟨5656608781052034810670805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3771072520701356540447203 5656608781052034810670805)
                  ·
                    refine ⟨132576768305907065875097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5656608781052034810670805 132576768305907065875097)
                    ·
                      rfl

theorem cell23_774577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_774577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774577 prefixEnd_774577 := by exact prefixLift 774577
  have htrace : WordTrace (prefixWord ++ tailWord_774577) baseStart_774577 baseEnd_774577 := by
    simpa [prefixWord, tailWord_774577, baseEnd_774577] using wordTrace_append hprefix tailTrace_774577
  have hstable : (prefixWord ++ tailWord_774577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774577).length < 2 ^ (prefixWord ++ tailWord_774577).sum := by decide
  have hdescent : baseEnd_774577 < baseStart_774577 := by decide
  rcases family_descends (prefixWord ++ tailWord_774577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774597 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_774597 : Nat := 118140960795 + 774597 * 2 ^ 59
def prefixEnd_774597 : Nat := 4983230072969 + 3 ^ 40 * 774597 * 2
def baseEnd_774597 : Nat := 397740574530811119375199

theorem tailTrace_774597 : CollatzResearch.WordTrace tailWord_774597 prefixEnd_774597 397740574530811119375199 := by
  unfold tailWord_774597
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251873574774834480514045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18834582383183222987009363 28251873574774834480514045)
  ·
    refine ⟨10594452590540562930192767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28251873574774834480514045 10594452590540562930192767)
    ·
      refine ⟨15891678885810844395289151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10594452590540562930192767 15891678885810844395289151)
      ·
        refine ⟨23837518328716266592933727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15891678885810844395289151 23837518328716266592933727)
        ·
          refine ⟨35756277493074399889400591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23837518328716266592933727 35756277493074399889400591)
          ·
            refine ⟨53634416239611599834100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35756277493074399889400591 53634416239611599834100887)
            ·
              refine ⟨80451624359417399751151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53634416239611599834100887 80451624359417399751151331)
              ·
                refine ⟨120677436539126099626726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80451624359417399751151331 120677436539126099626726997)
                ·
                  refine ⟨1414188709442883980000707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 120677436539126099626726997 1414188709442883980000707)
                  ·
                    refine ⟨2121283064164325970001061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414188709442883980000707 2121283064164325970001061)
                    ·
                      refine ⟨397740574530811119375199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2121283064164325970001061 397740574530811119375199)
                      ·
                        rfl

theorem cell23_774597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_774597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774597 prefixEnd_774597 := by exact prefixLift 774597
  have htrace : WordTrace (prefixWord ++ tailWord_774597) baseStart_774597 baseEnd_774597 := by
    simpa [prefixWord, tailWord_774597, baseEnd_774597] using wordTrace_append hprefix tailTrace_774597
  have hstable : (prefixWord ++ tailWord_774597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774597).length < 2 ^ (prefixWord ++ tailWord_774597).sum := by decide
  have hdescent : baseEnd_774597 < baseStart_774597 := by decide
  rcases family_descends (prefixWord ++ tailWord_774597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774626 : List Nat := [3, 3, 3, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_774626 : Nat := 118140960795 + 774626 * 2 ^ 59
def prefixEnd_774626 : Nat := 4983230072969 + 3 ^ 40 * 774626 * 2
def baseEnd_774626 : Nat := 397755465469791505912567

theorem tailTrace_774626 : CollatzResearch.WordTrace tailWord_774626 prefixEnd_774626 397755465469791505912567 := by
  unfold tailWord_774626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063232822917443108329933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18835287527779848288879821 7063232822917443108329933)
  ·
    refine ⟨2648712308594041165623725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7063232822917443108329933 2648712308594041165623725)
    ·
      refine ⟨993267115722765437108897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2648712308594041165623725 993267115722765437108897)
      ·
        refine ⟨744950336792074077831673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993267115722765437108897 744950336792074077831673)
        ·
          refine ⟨558712752594055558373755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744950336792074077831673 558712752594055558373755)
          ·
            refine ⟨838069128891083337560633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558712752594055558373755 838069128891083337560633)
            ·
              refine ⟨628551846668312503170475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838069128891083337560633 628551846668312503170475)
              ·
                refine ⟨942827770002468754755713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628551846668312503170475 942827770002468754755713)
                ·
                  refine ⟨707120827501851566066785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942827770002468754755713 707120827501851566066785)
                  ·
                    refine ⟨530340620626388674550089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707120827501851566066785 530340620626388674550089)
                    ·
                      refine ⟨397755465469791505912567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530340620626388674550089 397755465469791505912567)
                      ·
                        rfl

theorem cell23_774626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_774626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774626 prefixEnd_774626 := by exact prefixLift 774626
  have htrace : WordTrace (prefixWord ++ tailWord_774626) baseStart_774626 baseEnd_774626 := by
    simpa [prefixWord, tailWord_774626, baseEnd_774626] using wordTrace_append hprefix tailTrace_774626
  have hstable : (prefixWord ++ tailWord_774626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774626).length < 2 ^ (prefixWord ++ tailWord_774626).sum := by decide
  have hdescent : baseEnd_774626 < baseStart_774626 := by decide
  rcases family_descends (prefixWord ++ tailWord_774626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774684 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_774684 : Nat := 118140960795 + 774684 * 2 ^ 59
def prefixEnd_774684 : Nat := 4983230072969 + 3 ^ 40 * 774684 * 2
def baseEnd_774684 : Nat := 132595082449250759662433

theorem tailTrace_774684 : CollatzResearch.WordTrace tailWord_774684 prefixEnd_774684 132595082449250759662433 := by
  unfold tailWord_774684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127523362729824169465553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18836697816973098892620737 14127523362729824169465553)
  ·
    refine ⟨10595642522047368127099165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14127523362729824169465553 10595642522047368127099165)
    ·
      refine ⟨3973365945767763047662187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10595642522047368127099165 3973365945767763047662187)
      ·
        refine ⟨5960048918651644571493281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973365945767763047662187 5960048918651644571493281)
        ·
          refine ⟨4470036688988733428619961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960048918651644571493281 4470036688988733428619961)
          ·
            refine ⟨3352527516741550071464971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4470036688988733428619961 3352527516741550071464971)
            ·
              refine ⟨5028791275112325107197457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352527516741550071464971 5028791275112325107197457)
              ·
                refine ⟨3771593456334243830398093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028791275112325107197457 3771593456334243830398093)
                ·
                  refine ⟨1414347546125341436399285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3771593456334243830398093 1414347546125341436399285)
                  ·
                    refine ⟨132595082449250759662433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1414347546125341436399285 132595082449250759662433)
                    ·
                      rfl

theorem cell23_774684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_774684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774684 prefixEnd_774684 := by exact prefixLift 774684
  have htrace : WordTrace (prefixWord ++ tailWord_774684) baseStart_774684 baseEnd_774684 := by
    simpa [prefixWord, tailWord_774684, baseEnd_774684] using wordTrace_append hprefix tailTrace_774684
  have hstable : (prefixWord ++ tailWord_774684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774684).length < 2 ^ (prefixWord ++ tailWord_774684).sum := by decide
  have hdescent : baseEnd_774684 < baseStart_774684 := by decide
  rcases family_descends (prefixWord ++ tailWord_774684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774698 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_774698 : Nat := 118140960795 + 774698 * 2 ^ 59
def prefixEnd_774698 : Nat := 4983230072969 + 3 ^ 40 * 774698 * 2
def baseEnd_774698 : Nat := 397792436076915224212235

theorem tailTrace_774698 : CollatzResearch.WordTrace tailWord_774698 prefixEnd_774698 397792436076915224212235 := by
  unfold tailWord_774698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063889336852232182485187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18837038231605952486627165 7063889336852232182485187)
  ·
    refine ⟨10595834005278348273727781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7063889336852232182485187 10595834005278348273727781)
    ·
      refine ⟨1986718875989690301323959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10595834005278348273727781 1986718875989690301323959)
      ·
        refine ⟨2980078313984535451985939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986718875989690301323959 2980078313984535451985939)
        ·
          refine ⟨4470117470976803177978909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980078313984535451985939 4470117470976803177978909)
          ·
            refine ⟨1676294051616301191742091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4470117470976803177978909 1676294051616301191742091)
            ·
              refine ⟨2514441077424451787613137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676294051616301191742091 2514441077424451787613137)
              ·
                refine ⟨1885830808068338840709853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514441077424451787613137 1885830808068338840709853)
                ·
                  refine ⟨707186553025627065266195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1885830808068338840709853 707186553025627065266195)
                  ·
                    refine ⟨1060779829538440597899293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707186553025627065266195 1060779829538440597899293)
                    ·
                      refine ⟨397792436076915224212235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060779829538440597899293 397792436076915224212235)
                      ·
                        rfl

theorem cell23_774698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_774698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774698 prefixEnd_774698 := by exact prefixLift 774698
  have htrace : WordTrace (prefixWord ++ tailWord_774698) baseStart_774698 baseEnd_774698 := by
    simpa [prefixWord, tailWord_774698, baseEnd_774698] using wordTrace_append hprefix tailTrace_774698
  have hstable : (prefixWord ++ tailWord_774698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774698).length < 2 ^ (prefixWord ++ tailWord_774698).sum := by decide
  have hdescent : baseEnd_774698 < baseStart_774698 := by decide
  rcases family_descends (prefixWord ++ tailWord_774698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774704 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_774704 : Nat := 118140960795 + 774704 * 2 ^ 59
def prefixEnd_774704 : Nat := 4983230072969 + 3 ^ 40 * 774704 * 2
def baseEnd_774704 : Nat := 397795516960842200737207

theorem tailTrace_774704 : CollatzResearch.WordTrace tailWord_774704 prefixEnd_774704 397795516960842200737207 := by
  unfold tailWord_774704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127888092693595877329583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18837184123591461169772777 14127888092693595877329583)
  ·
    refine ⟨21191832139040393815994375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14127888092693595877329583 21191832139040393815994375)
    ·
      refine ⟨31787748208560590723991563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21191832139040393815994375 31787748208560590723991563)
      ·
        refine ⟨47681622312840886085987345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31787748208560590723991563 47681622312840886085987345)
        ·
          refine ⟨35761216734630664564490509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47681622312840886085987345 35761216734630664564490509)
          ·
            refine ⟨13410456275486499211683941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35761216734630664564490509 13410456275486499211683941)
            ·
              refine ⟨2514460551653718602190739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13410456275486499211683941 2514460551653718602190739)
              ·
                refine ⟨3771690827480577903286109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514460551653718602190739 3771690827480577903286109)
                ·
                  refine ⟨1414384060305216713732291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3771690827480577903286109 1414384060305216713732291)
                  ·
                    refine ⟨2121576090457825070598437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1414384060305216713732291 2121576090457825070598437)
                    ·
                      refine ⟨397795516960842200737207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2121576090457825070598437 397795516960842200737207)
                      ·
                        rfl

theorem cell23_774704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_774704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774704 prefixEnd_774704 := by exact prefixLift 774704
  have htrace : WordTrace (prefixWord ++ tailWord_774704) baseStart_774704 baseEnd_774704 := by
    simpa [prefixWord, tailWord_774704, baseEnd_774704] using wordTrace_append hprefix tailTrace_774704
  have hstable : (prefixWord ++ tailWord_774704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774704).length < 2 ^ (prefixWord ++ tailWord_774704).sum := by decide
  have hdescent : baseEnd_774704 < baseStart_774704 := by decide
  rcases family_descends (prefixWord ++ tailWord_774704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774714 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 6]
def baseStart_774714 : Nat := 118140960795 + 774714 * 2 ^ 59
def prefixEnd_774714 : Nat := 4983230072969 + 3 ^ 40 * 774714 * 2
def baseEnd_774714 : Nat := 132600217255795720537387

theorem tailTrace_774714 : CollatzResearch.WordTrace tailWord_774714 prefixEnd_774714 132600217255795720537387 := by
  unfold tailWord_774714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064035228837740865630799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18837427276900642308348797 7064035228837740865630799)
  ·
    refine ⟨10596052843256611298446199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064035228837740865630799 10596052843256611298446199)
    ·
      refine ⟨15894079264884916947669299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596052843256611298446199 15894079264884916947669299)
      ·
        refine ⟨23841118897327375421503949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894079264884916947669299 23841118897327375421503949)
        ·
          refine ⟨8940419586497765783063981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23841118897327375421503949 8940419586497765783063981)
          ·
            refine ⟨3352657344936662168648993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8940419586497765783063981 3352657344936662168648993)
            ·
              refine ⟨2514493008702496626486745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352657344936662168648993 2514493008702496626486745)
              ·
                refine ⟨1885869756526872469865059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514493008702496626486745 1885869756526872469865059)
                ·
                  refine ⟨2828804634790308704797589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885869756526872469865059 2828804634790308704797589)
                  ·
                    refine ⟨132600217255795720537387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2828804634790308704797589 132600217255795720537387)
                    ·
                      rfl

theorem cell23_774714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_774714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774714 prefixEnd_774714 := by exact prefixLift 774714
  have htrace : WordTrace (prefixWord ++ tailWord_774714) baseStart_774714 baseEnd_774714 := by
    simpa [prefixWord, tailWord_774714, baseEnd_774714] using wordTrace_append hprefix tailTrace_774714
  have hstable : (prefixWord ++ tailWord_774714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774714).length < 2 ^ (prefixWord ++ tailWord_774714).sum := by decide
  have hdescent : baseEnd_774714 < baseStart_774714 := by decide
  rcases family_descends (prefixWord ++ tailWord_774714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774731 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 2, 4]
def baseStart_774731 : Nat := 118140960795 + 774731 * 2 ^ 59
def prefixEnd_774731 : Nat := 4983230072969 + 3 ^ 40 * 774731 * 2
def baseEnd_774731 : Nat := 132603126979504531699861

theorem tailTrace_774731 : CollatzResearch.WordTrace tailWord_774731 prefixEnd_774731 132603126979504531699861 := by
  unfold tailWord_774731
  simp only [CollatzResearch.WordTrace]
  refine ⟨28256760956289375365892047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18837840637526250243928031 28256760956289375365892047)
  ·
    refine ⟨42385141434434063048838071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28256760956289375365892047 42385141434434063048838071)
    ·
      refine ⟨63577712151651094573257107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42385141434434063048838071 63577712151651094573257107)
      ·
        refine ⟨95366568227476641859885661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63577712151651094573257107 95366568227476641859885661)
        ·
          refine ⟨35762463085303740697457123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95366568227476641859885661 35762463085303740697457123)
          ·
            refine ⟨53643694627955611046185685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35762463085303740697457123 53643694627955611046185685)
            ·
              refine ⟨1257274092842709633894977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53643694627955611046185685 1257274092842709633894977)
              ·
                refine ⟨942955569632032225421233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257274092842709633894977 942955569632032225421233)
                ·
                  refine ⟨707216677224024169065925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 942955569632032225421233 707216677224024169065925)
                  ·
                    refine ⟨132603126979504531699861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707216677224024169065925 132603126979504531699861)
                    ·
                      rfl

theorem cell23_774731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 4].length) (baseStart_774731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774731 prefixEnd_774731 := by exact prefixLift 774731
  have htrace : WordTrace (prefixWord ++ tailWord_774731) baseStart_774731 baseEnd_774731 := by
    simpa [prefixWord, tailWord_774731, baseEnd_774731] using wordTrace_append hprefix tailTrace_774731
  have hstable : (prefixWord ++ tailWord_774731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774731).length < 2 ^ (prefixWord ++ tailWord_774731).sum := by decide
  have hdescent : baseEnd_774731 < baseStart_774731 := by decide
  rcases family_descends (prefixWord ++ tailWord_774731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774734 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_774734 : Nat := 118140960795 + 774734 * 2 ^ 59
def prefixEnd_774734 : Nat := 4983230072969 + 3 ^ 40 * 774734 * 2
def baseEnd_774734 : Nat := 397810921380477083362069

theorem tailTrace_774734 : CollatzResearch.WordTrace tailWord_774734 prefixEnd_774734 397810921380477083362069 := by
  unfold tailWord_774734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532108796909813359781407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18837913583519004585500837 3532108796909813359781407)
  ·
    refine ⟨5298163195364720039672111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532108796909813359781407 5298163195364720039672111)
    ·
      refine ⟨7947244793047080059508167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298163195364720039672111 7947244793047080059508167)
      ·
        refine ⟨11920867189570620089262251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7947244793047080059508167 11920867189570620089262251)
        ·
          refine ⟨17881300784355930133893377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11920867189570620089262251 17881300784355930133893377)
          ·
            refine ⟨13410975588266947600420033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17881300784355930133893377 13410975588266947600420033)
            ·
              refine ⟨10058231691200210700315025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13410975588266947600420033 10058231691200210700315025)
              ·
                refine ⟨7543673768400158025236269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10058231691200210700315025 7543673768400158025236269)
                ·
                  refine ⟨2828877663150059259463601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7543673768400158025236269 2828877663150059259463601)
                  ·
                    refine ⟨2121658247362544444597701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2828877663150059259463601 2121658247362544444597701)
                    ·
                      refine ⟨397810921380477083362069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2121658247362544444597701 397810921380477083362069)
                      ·
                        rfl

theorem cell23_774734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_774734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774734 prefixEnd_774734 := by exact prefixLift 774734
  have htrace : WordTrace (prefixWord ++ tailWord_774734) baseStart_774734 baseEnd_774734 := by
    simpa [prefixWord, tailWord_774734, baseEnd_774734] using wordTrace_append hprefix tailTrace_774734
  have hstable : (prefixWord ++ tailWord_774734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774734).length < 2 ^ (prefixWord ++ tailWord_774734).sum := by decide
  have hdescent : baseEnd_774734 < baseStart_774734 := by decide
  rcases family_descends (prefixWord ++ tailWord_774734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774748 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_774748 : Nat := 118140960795 + 774748 * 2 ^ 59
def prefixEnd_774748 : Nat := 4983230072969 + 3 ^ 40 * 774748 * 2
def baseEnd_774748 : Nat := 132606036703213342862335

theorem tailTrace_774748 : CollatzResearch.WordTrace tailWord_774748 prefixEnd_774748 132606036703213342862335 := by
  unfold tailWord_774748
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128690498613893634630449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18838253998151858179507265 14128690498613893634630449)
  ·
    refine ⟨10596517873960420225972837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14128690498613893634630449 10596517873960420225972837)
    ·
      refine ⟨1986847101367578792369907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10596517873960420225972837 1986847101367578792369907)
      ·
        refine ⟨2980270652051368188554861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986847101367578792369907 2980270652051368188554861)
        ·
          refine ⟨1117601494519263070708073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2980270652051368188554861 1117601494519263070708073)
          ·
            refine ⟨838201120889447303031055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117601494519263070708073 838201120889447303031055)
            ·
              refine ⟨1257301681334170954546583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838201120889447303031055 1257301681334170954546583)
              ·
                refine ⟨1885952522001256431819875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257301681334170954546583 1885952522001256431819875)
                ·
                  refine ⟨2828928783001884647729813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885952522001256431819875 2828928783001884647729813)
                  ·
                    refine ⟨132606036703213342862335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2828928783001884647729813 132606036703213342862335)
                    ·
                      rfl

theorem cell23_774748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_774748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774748 prefixEnd_774748 := by exact prefixLift 774748
  have htrace : WordTrace (prefixWord ++ tailWord_774748) baseStart_774748 baseEnd_774748 := by
    simpa [prefixWord, tailWord_774748, baseEnd_774748] using wordTrace_append hprefix tailTrace_774748
  have hstable : (prefixWord ++ tailWord_774748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774748).length < 2 ^ (prefixWord ++ tailWord_774748).sum := by decide
  have hdescent : baseEnd_774748 < baseStart_774748 := by decide
  rcases family_descends (prefixWord ++ tailWord_774748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774788 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_774788 : Nat := 118140960795 + 774788 * 2 ^ 59
def prefixEnd_774788 : Nat := 4983230072969 + 3 ^ 40 * 774788 * 2
def baseEnd_774788 : Nat := 397838649335819872086821

theorem tailTrace_774788 : CollatzResearch.WordTrace tailWord_774788 prefixEnd_774788 397838649335819872086821 := by
  unfold tailWord_774788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129419958541437050358509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18839226611388582733811345 14129419958541437050358509)
  ·
    refine ⟨5298532484453038893884441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14129419958541437050358509 5298532484453038893884441)
    ·
      refine ⟨3973899363339779170413331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5298532484453038893884441 3973899363339779170413331)
      ·
        refine ⟨5960849045009668755619997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973899363339779170413331 5960849045009668755619997)
        ·
          refine ⟨2235318391878625783357499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5960849045009668755619997 2235318391878625783357499)
          ·
            refine ⟨3352977587817938675036249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235318391878625783357499 3352977587817938675036249)
            ·
              refine ⟨2514733190863454006277187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352977587817938675036249 2514733190863454006277187)
              ·
                refine ⟨3772099786295181009415781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514733190863454006277187 3772099786295181009415781)
                ·
                  refine ⟨707268709930346439265459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3772099786295181009415781 707268709930346439265459)
                  ·
                    refine ⟨1060903064895519658898189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 707268709930346439265459 1060903064895519658898189)
                    ·
                      refine ⟨397838649335819872086821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1060903064895519658898189 397838649335819872086821)
                      ·
                        rfl

theorem cell23_774788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_774788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774788 prefixEnd_774788 := by exact prefixLift 774788
  have htrace : WordTrace (prefixWord ++ tailWord_774788) baseStart_774788 baseEnd_774788 := by
    simpa [prefixWord, tailWord_774788, baseEnd_774788] using wordTrace_append hprefix tailTrace_774788
  have hstable : (prefixWord ++ tailWord_774788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774788).length < 2 ^ (prefixWord ++ tailWord_774788).sum := by decide
  have hdescent : baseEnd_774788 < baseStart_774788 := by decide
  rcases family_descends (prefixWord ++ tailWord_774788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774798 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_774798 : Nat := 118140960795 + 774798 * 2 ^ 59
def prefixEnd_774798 : Nat := 4983230072969 + 3 ^ 40 * 774798 * 2
def baseEnd_774798 : Nat := 397843784142364832961775

theorem tailTrace_774798 : CollatzResearch.WordTrace tailWord_774798 prefixEnd_774798 397843784142364832961775 := by
  unfold tailWord_774798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532400580880830726072631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18839469764697763872387365 3532400580880830726072631)
  ·
    refine ⟨5298600871321246089108947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3532400580880830726072631 5298600871321246089108947)
    ·
      refine ⟨7947901306981869133663421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298600871321246089108947 7947901306981869133663421)
      ·
        refine ⟨2980462990118200925123783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7947901306981869133663421 2980462990118200925123783)
        ·
          refine ⟨4470694485177301387685675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980462990118200925123783 4470694485177301387685675)
          ·
            refine ⟨6706041727765952081528513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470694485177301387685675 6706041727765952081528513)
            ·
              refine ⟨5029531295824464061146385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6706041727765952081528513 5029531295824464061146385)
              ·
                refine ⟨3772148471868348045859789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5029531295824464061146385 3772148471868348045859789)
                ·
                  refine ⟨1414555676950630517197421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3772148471868348045859789 1414555676950630517197421)
                  ·
                    refine ⟨530458378856486443949033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414555676950630517197421 530458378856486443949033)
                    ·
                      refine ⟨397843784142364832961775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530458378856486443949033 397843784142364832961775)
                      ·
                        rfl

theorem cell23_774798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_774798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774798 prefixEnd_774798 := by exact prefixLift 774798
  have htrace : WordTrace (prefixWord ++ tailWord_774798) baseStart_774798 baseEnd_774798 := by
    simpa [prefixWord, tailWord_774798, baseEnd_774798] using wordTrace_append hprefix tailTrace_774798
  have hstable : (prefixWord ++ tailWord_774798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774798).length < 2 ^ (prefixWord ++ tailWord_774798).sum := by decide
  have hdescent : baseEnd_774798 < baseStart_774798 := by decide
  rcases family_descends (prefixWord ++ tailWord_774798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774845 : List Nat := [1, 4, 1, 2, 1, 3, 1, 4, 2, 2, 2]
def baseStart_774845 : Nat := 118140960795 + 774845 * 2 ^ 59
def prefixEnd_774845 : Nat := 4983230072969 + 3 ^ 40 * 774845 * 2
def baseEnd_774845 : Nat := 397867917733126149074059

theorem tailTrace_774845 : CollatzResearch.WordTrace tailWord_774845 prefixEnd_774845 397867917733126149074059 := by
  unfold tailWord_774845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260918877876372835541989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18840612585250915223694659 28260918877876372835541989)
  ·
    refine ⟨5298922289601819906664123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28260918877876372835541989 5298922289601819906664123)
    ·
      refine ⟨7948383434402729859996185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298922289601819906664123 7948383434402729859996185)
      ·
        refine ⟨5961287575802047394997139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7948383434402729859996185 5961287575802047394997139)
        ·
          refine ⟨8941931363703071092495709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5961287575802047394997139 8941931363703071092495709)
          ·
            refine ⟨3353224261388651659685891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8941931363703071092495709 3353224261388651659685891)
            ·
              refine ⟨5029836392082977489528837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353224261388651659685891 5029836392082977489528837)
              ·
                refine ⟨943094323515558279286657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5029836392082977489528837 943094323515558279286657)
                ·
                  refine ⟨707320742636668709464993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 943094323515558279286657 707320742636668709464993)
                  ·
                    refine ⟨530490556977501532098745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707320742636668709464993 530490556977501532098745)
                    ·
                      refine ⟨397867917733126149074059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530490556977501532098745 397867917733126149074059)
                      ·
                        rfl

theorem cell23_774845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_774845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774845 prefixEnd_774845 := by exact prefixLift 774845
  have htrace : WordTrace (prefixWord ++ tailWord_774845) baseStart_774845 baseEnd_774845 := by
    simpa [prefixWord, tailWord_774845, baseEnd_774845] using wordTrace_append hprefix tailTrace_774845
  have hstable : (prefixWord ++ tailWord_774845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774845).length < 2 ^ (prefixWord ++ tailWord_774845).sum := by decide
  have hdescent : baseEnd_774845 < baseStart_774845 := by decide
  rcases family_descends (prefixWord ++ tailWord_774845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774868 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 7]
def baseStart_774868 : Nat := 118140960795 + 774868 * 2 ^ 59
def prefixEnd_774868 : Nat := 4983230072969 + 3 ^ 40 * 774868 * 2
def baseEnd_774868 : Nat := 44208858643131062120717

theorem tailTrace_774868 : CollatzResearch.WordTrace tailWord_774868 prefixEnd_774868 44208858643131062120717 := by
  unfold tailWord_774868
  simp only [CollatzResearch.WordTrace]
  refine ⟨14130878878396523881814629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18841171837862031842419505 14130878878396523881814629)
  ·
    refine ⟨2649539789699348227840243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14130878878396523881814629 2649539789699348227840243)
    ·
      refine ⟨3974309684549022341760365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2649539789699348227840243 3974309684549022341760365)
      ·
        refine ⟨1490366131705883378160137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3974309684549022341760365 1490366131705883378160137)
        ·
          refine ⟨1117774598779412533620103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490366131705883378160137 1117774598779412533620103)
          ·
            refine ⟨1676661898169118800430155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117774598779412533620103 1676661898169118800430155)
            ·
              refine ⟨2514992847253678200645233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676661898169118800430155 2514992847253678200645233)
              ·
                refine ⟨1886244635440258650483925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514992847253678200645233 1886244635440258650483925)
                ·
                  refine ⟨44208858643131062120717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1886244635440258650483925 44208858643131062120717)
                  ·
                    rfl

theorem cell23_774868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_774868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774868 prefixEnd_774868 := by exact prefixLift 774868
  have htrace : WordTrace (prefixWord ++ tailWord_774868) baseStart_774868 baseEnd_774868 := by
    simpa [prefixWord, tailWord_774868, baseEnd_774868] using wordTrace_append hprefix tailTrace_774868
  have hstable : (prefixWord ++ tailWord_774868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774868).length < 2 ^ (prefixWord ++ tailWord_774868).sum := by decide
  have hdescent : baseEnd_774868 < baseStart_774868 := by decide
  rcases family_descends (prefixWord ++ tailWord_774868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774881 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 7]
def baseStart_774881 : Nat := 118140960795 + 774881 * 2 ^ 59
def prefixEnd_774881 : Nat := 4983230072969 + 3 ^ 40 * 774881 * 2
def baseEnd_774881 : Nat := 132628801012229336074631

theorem tailTrace_774881 : CollatzResearch.WordTrace tailWord_774881 prefixEnd_774881 132628801012229336074631 := by
  unfold tailWord_774881
  simp only [CollatzResearch.WordTrace]
  refine ⟨28262231905745950983852497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18841487937163967322568331 28262231905745950983852497)
  ·
    refine ⟨21196673929309463237889373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28262231905745950983852497 21196673929309463237889373)
    ·
      refine ⟨7948752723491048714208515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21196673929309463237889373 7948752723491048714208515)
      ·
        refine ⟨11923129085236573071312773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7948752723491048714208515 11923129085236573071312773)
        ·
          refine ⟨2235586703481857450871145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11923129085236573071312773 2235586703481857450871145)
          ·
            refine ⟨1676690027611393088153359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235586703481857450871145 1676690027611393088153359)
            ·
              refine ⟨2515035041417089632230039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676690027611393088153359 2515035041417089632230039)
              ·
                refine ⟨3772552562125634448345059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515035041417089632230039 3772552562125634448345059)
                ·
                  refine ⟨5658828843188451672517589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772552562125634448345059 5658828843188451672517589)
                  ·
                    refine ⟨132628801012229336074631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5658828843188451672517589 132628801012229336074631)
                    ·
                      rfl

theorem cell23_774881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_774881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774881 prefixEnd_774881 := by exact prefixLift 774881
  have htrace : WordTrace (prefixWord ++ tailWord_774881) baseStart_774881 baseEnd_774881 := by
    simpa [prefixWord, tailWord_774881, baseEnd_774881] using wordTrace_append hprefix tailTrace_774881
  have hstable : (prefixWord ++ tailWord_774881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774881).length < 2 ^ (prefixWord ++ tailWord_774881).sum := by decide
  have hdescent : baseEnd_774881 < baseStart_774881 := by decide
  rcases family_descends (prefixWord ++ tailWord_774881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774921 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 3]
def baseStart_774921 : Nat := 118140960795 + 774921 * 2 ^ 59
def prefixEnd_774921 : Nat := 4983230072969 + 3 ^ 40 * 774921 * 2
def baseEnd_774921 : Nat := 397906942262867851723709

theorem tailTrace_774921 : CollatzResearch.WordTrace tailWord_774921 prefixEnd_774921 397906942262867851723709 := by
  unfold tailWord_774921
  simp only [CollatzResearch.WordTrace]
  refine ⟨28263690825601037815308617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18842460550400691876872411 28263690825601037815308617)
  ·
    refine ⟨21197768119200778361481463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28263690825601037815308617 21197768119200778361481463)
    ·
      refine ⟨31796652178801167542222195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21197768119200778361481463 31796652178801167542222195)
      ·
        refine ⟨47694978268201751313333293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31796652178801167542222195 47694978268201751313333293)
        ·
          refine ⟨17885616850575656742499985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47694978268201751313333293 17885616850575656742499985)
          ·
            refine ⟨13414212637931742556874989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17885616850575656742499985 13414212637931742556874989)
            ·
              refine ⟨5030329739224403458828121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13414212637931742556874989 5030329739224403458828121)
              ·
                refine ⟨3772747304418302594121091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030329739224403458828121 3772747304418302594121091)
                ·
                  refine ⟨5659120956627453891181637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772747304418302594121091 5659120956627453891181637)
                  ·
                    refine ⟨1061085179367647604596557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5659120956627453891181637 1061085179367647604596557)
                    ·
                      refine ⟨397906942262867851723709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1061085179367647604596557 397906942262867851723709)
                      ·
                        rfl

theorem cell23_774921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_774921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774921 prefixEnd_774921 := by exact prefixLift 774921
  have htrace : WordTrace (prefixWord ++ tailWord_774921) baseStart_774921 baseEnd_774921 := by
    simpa [prefixWord, tailWord_774921, baseEnd_774921] using wordTrace_append hprefix tailTrace_774921
  have hstable : (prefixWord ++ tailWord_774921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774921).length < 2 ^ (prefixWord ++ tailWord_774921).sum := by decide
  have hdescent : baseEnd_774921 < baseStart_774921 := by decide
  rcases family_descends (prefixWord ++ tailWord_774921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774938 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_774938 : Nat := 118140960795 + 774938 * 2 ^ 59
def prefixEnd_774938 : Nat := 4983230072969 + 3 ^ 40 * 774938 * 2
def baseEnd_774938 : Nat := 397915671433994285211131

theorem tailTrace_774938 : CollatzResearch.WordTrace tailWord_774938 prefixEnd_774938 397915671433994285211131 := by
  unfold tailWord_774938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066077716634862429669367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18842873911026299812451645 7066077716634862429669367)
  ·
    refine ⟨10599116574952293644504051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066077716634862429669367 10599116574952293644504051)
    ·
      refine ⟨15898674862428440466756077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599116574952293644504051 15898674862428440466756077)
      ·
        refine ⟨5962003073410665175033529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15898674862428440466756077 5962003073410665175033529)
        ·
          refine ⟨4471502305057998881275147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5962003073410665175033529 4471502305057998881275147)
          ·
            refine ⟨6707253457586998321912721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471502305057998881275147 6707253457586998321912721)
            ·
              refine ⟨5030440093190248741434541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6707253457586998321912721 5030440093190248741434541)
              ·
                refine ⟨1886415034946343278037953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5030440093190248741434541 1886415034946343278037953)
                ·
                  refine ⟨1414811276209757458528465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1886415034946343278037953 1414811276209757458528465)
                  ·
                    refine ⟨1061108457157318093896349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1414811276209757458528465 1061108457157318093896349)
                    ·
                      refine ⟨397915671433994285211131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1061108457157318093896349 397915671433994285211131)
                      ·
                        rfl

theorem cell23_774938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_774938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774938 prefixEnd_774938 := by exact prefixLift 774938
  have htrace : WordTrace (prefixWord ++ tailWord_774938) baseStart_774938 baseEnd_774938 := by
    simpa [prefixWord, tailWord_774938, baseEnd_774938] using wordTrace_append hprefix tailTrace_774938
  have hstable : (prefixWord ++ tailWord_774938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774938).length < 2 ^ (prefixWord ++ tailWord_774938).sum := by decide
  have hdescent : baseEnd_774938 < baseStart_774938 := by decide
  rcases family_descends (prefixWord ++ tailWord_774938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774958 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_774958 : Nat := 118140960795 + 774958 * 2 ^ 59
def prefixEnd_774958 : Nat := 4983230072969 + 3 ^ 40 * 774958 * 2
def baseEnd_774958 : Nat := 44213993449676022995671

theorem tailTrace_774958 : CollatzResearch.WordTrace tailWord_774958 prefixEnd_774958 44213993449676022995671 := by
  unfold tailWord_774958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533130040808374141800691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18843360217644662089603685 3533130040808374141800691)
  ·
    refine ⟨5299695061212561212701037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533130040808374141800691 5299695061212561212701037)
    ·
      refine ⟨1987385647954710454762889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5299695061212561212701037 1987385647954710454762889)
      ·
        refine ⟨1490539235966032841072167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1987385647954710454762889 1490539235966032841072167)
        ·
          refine ⟨2235808853949049261608251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490539235966032841072167 2235808853949049261608251)
          ·
            refine ⟨3353713280923573892412377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235808853949049261608251 3353713280923573892412377)
            ·
              refine ⟨2515284960692680419309283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3353713280923573892412377 2515284960692680419309283)
              ·
                refine ⟨3772927441039020628963925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515284960692680419309283 3772927441039020628963925)
                ·
                  refine ⟨44213993449676022995671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3772927441039020628963925 44213993449676022995671)
                  ·
                    rfl

theorem cell23_774958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_774958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774958 prefixEnd_774958 := by exact prefixLift 774958
  have htrace : WordTrace (prefixWord ++ tailWord_774958) baseStart_774958 baseEnd_774958 := by
    simpa [prefixWord, tailWord_774958, baseEnd_774958] using wordTrace_append hprefix tailTrace_774958
  have hstable : (prefixWord ++ tailWord_774958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774958).length < 2 ^ (prefixWord ++ tailWord_774958).sum := by decide
  have hdescent : baseEnd_774958 < baseStart_774958 := by decide
  rcases family_descends (prefixWord ++ tailWord_774958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774962 : List Nat := [3, 2, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_774962 : Nat := 118140960795 + 774962 * 2 ^ 59
def prefixEnd_774962 : Nat := 4983230072969 + 3 ^ 40 * 774962 * 2
def baseEnd_774962 : Nat := 132642664989900730437007

theorem tailTrace_774962 : CollatzResearch.WordTrace tailWord_774962 prefixEnd_774962 132642664989900730437007 := by
  unfold tailWord_774962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066296554613125454387785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18843457478968334545034093 7066296554613125454387785)
  ·
    refine ⟨5299722415959844090790839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7066296554613125454387785 5299722415959844090790839)
    ·
      refine ⟨7949583623939766136186259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299722415959844090790839 7949583623939766136186259)
      ·
        refine ⟨11924375435909649204279389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949583623939766136186259 11924375435909649204279389)
        ·
          refine ⟨4471640788466118451604771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11924375435909649204279389 4471640788466118451604771)
          ·
            refine ⟨6707461182699177677407157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471640788466118451604771 6707461182699177677407157)
            ·
              refine ⟨628824485878047907256921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6707461182699177677407157 628824485878047907256921)
              ·
                refine ⟨471618364408535930442691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628824485878047907256921 471618364408535930442691)
                ·
                  refine ⟨707427546612803895664037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471618364408535930442691 707427546612803895664037)
                  ·
                    refine ⟨132642664989900730437007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707427546612803895664037 132642664989900730437007)
                    ·
                      rfl

theorem cell23_774962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_774962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774962 prefixEnd_774962 := by exact prefixLift 774962
  have htrace : WordTrace (prefixWord ++ tailWord_774962) baseStart_774962 baseEnd_774962 := by
    simpa [prefixWord, tailWord_774962, baseEnd_774962] using wordTrace_append hprefix tailTrace_774962
  have hstable : (prefixWord ++ tailWord_774962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774962).length < 2 ^ (prefixWord ++ tailWord_774962).sum := by decide
  have hdescent : baseEnd_774962 < baseStart_774962 := by decide
  rcases family_descends (prefixWord ++ tailWord_774962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774975 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 6]
def baseStart_774975 : Nat := 118140960795 + 774975 * 2 ^ 59
def prefixEnd_774975 : Nat := 4983230072969 + 3 ^ 40 * 774975 * 2
def baseEnd_774975 : Nat := 44214963357578960049829

theorem tailTrace_774975 : CollatzResearch.WordTrace tailWord_774975 prefixEnd_774975 44214963357578960049829 := by
  unfold tailWord_774975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28265660367405405037774379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18843773578270270025182919 28265660367405405037774379)
  ·
    refine ⟨42398490551108107556661569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28265660367405405037774379 42398490551108107556661569)
    ·
      refine ⟨31798867913331080667496177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42398490551108107556661569 31798867913331080667496177)
      ·
        refine ⟨23849150934998310500622133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31798867913331080667496177 23849150934998310500622133)
        ·
          refine ⟨2235857900156091609433325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23849150934998310500622133 2235857900156091609433325)
          ·
            refine ⟨838446712558534353537497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2235857900156091609433325 838446712558534353537497)
            ·
              refine ⟨628835034418900765153123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838446712558534353537497 628835034418900765153123)
              ·
                refine ⟨943252551628351147729685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 628835034418900765153123 943252551628351147729685)
                ·
                  refine ⟨44214963357578960049829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 943252551628351147729685 44214963357578960049829)
                  ·
                    rfl

theorem cell23_774975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 6].length) (baseStart_774975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774975 prefixEnd_774975 := by exact prefixLift 774975
  have htrace : WordTrace (prefixWord ++ tailWord_774975) baseStart_774975 baseEnd_774975 := by
    simpa [prefixWord, tailWord_774975, baseEnd_774975] using wordTrace_append hprefix tailTrace_774975
  have hstable : (prefixWord ++ tailWord_774975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774975).length < 2 ^ (prefixWord ++ tailWord_774975).sum := by decide
  have hdescent : baseEnd_774975 < baseStart_774975 := by decide
  rcases family_descends (prefixWord ++ tailWord_774975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_774988 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_774988 : Nat := 118140960795 + 774988 * 2 ^ 59
def prefixEnd_774988 : Nat := 4983230072969 + 3 ^ 40 * 774988 * 2
def baseEnd_774988 : Nat := 132647115155573029861967

theorem tailTrace_774988 : CollatzResearch.WordTrace tailWord_774988 prefixEnd_774988 132647115155573029861967 := by
  unfold tailWord_774988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14133067258179154128998809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18844089677572205505331745 14133067258179154128998809)
  ·
    refine ⟨10599800443634365596749107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14133067258179154128998809 10599800443634365596749107)
    ·
      refine ⟨15899700665451548395123661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599800443634365596749107 15899700665451548395123661)
      ·
        refine ⟨5962387749544330648171373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15899700665451548395123661 5962387749544330648171373)
        ·
          refine ⟨2235895406079123993064265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5962387749544330648171373 2235895406079123993064265)
          ·
            refine ⟨1676921554559342994798199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235895406079123993064265 1676921554559342994798199)
            ·
              refine ⟨2515382331839014492197299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676921554559342994798199 2515382331839014492197299)
              ·
                refine ⟨3773073497758521738295949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2515382331839014492197299 3773073497758521738295949)
                ·
                  refine ⟨1414902561659445651860981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3773073497758521738295949 1414902561659445651860981)
                  ·
                    refine ⟨132647115155573029861967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1414902561659445651860981 132647115155573029861967)
                    ·
                      rfl

theorem cell23_774988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_774988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_774988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_774988 prefixEnd_774988 := by exact prefixLift 774988
  have htrace : WordTrace (prefixWord ++ tailWord_774988) baseStart_774988 baseEnd_774988 := by
    simpa [prefixWord, tailWord_774988, baseEnd_774988] using wordTrace_append hprefix tailTrace_774988
  have hstable : (prefixWord ++ tailWord_774988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_774988).length < 2 ^ (prefixWord ++ tailWord_774988).sum := by decide
  have hdescent : baseEnd_774988 < baseStart_774988 := by decide
  rcases family_descends (prefixWord ++ tailWord_774988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775001 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 6]
def baseStart_775001 : Nat := 118140960795 + 775001 * 2 ^ 59
def prefixEnd_775001 : Nat := 4983230072969 + 3 ^ 40 * 775001 * 2
def baseEnd_775001 : Nat := 132649340238409179574447

theorem tailTrace_775001 : CollatzResearch.WordTrace tailWord_775001 prefixEnd_775001 132649340238409179574447 := by
  unfold tailWord_775001
  simp only [CollatzResearch.WordTrace]
  refine ⟨28266608665311211478220857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18844405776874140985480571 28266608665311211478220857)
  ·
    refine ⟨21199956498983408608665643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28266608665311211478220857 21199956498983408608665643)
    ·
      refine ⟨31799934748475112912998465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21199956498983408608665643 31799934748475112912998465)
      ·
        refine ⟨23849951061356334684748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31799934748475112912998465 23849951061356334684748849)
        ·
          refine ⟨17887463296017251013561637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23849951061356334684748849 17887463296017251013561637)
          ·
            refine ⟨3353899368003234565042807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17887463296017251013561637 3353899368003234565042807)
            ·
              refine ⟨5030849052004851847564211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353899368003234565042807 5030849052004851847564211)
              ·
                refine ⟨7546273578007277771346317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030849052004851847564211 7546273578007277771346317)
                ·
                  refine ⟨2829852591752729164254869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7546273578007277771346317 2829852591752729164254869)
                  ·
                    refine ⟨132649340238409179574447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2829852591752729164254869 132649340238409179574447)
                    ·
                      rfl

theorem cell23_775001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 6].length) (baseStart_775001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775001 prefixEnd_775001 := by exact prefixLift 775001
  have htrace : WordTrace (prefixWord ++ tailWord_775001) baseStart_775001 baseEnd_775001 := by
    simpa [prefixWord, tailWord_775001, baseEnd_775001] using wordTrace_append hprefix tailTrace_775001
  have hstable : (prefixWord ++ tailWord_775001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775001).length < 2 ^ (prefixWord ++ tailWord_775001).sum := by decide
  have hdescent : baseEnd_775001 < baseStart_775001 := by decide
  rcases family_descends (prefixWord ++ tailWord_775001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775091 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 8]
def baseStart_775091 : Nat := 118140960795 + 775091 * 2 ^ 59
def prefixEnd_775091 : Nat := 4983230072969 + 3 ^ 40 * 775091 * 2
def baseEnd_775091 : Nat := 132664744658044062199309

theorem tailTrace_775091 : CollatzResearch.WordTrace tailWord_775091 prefixEnd_775091 132664744658044062199309 := by
  unfold tailWord_775091
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269891234985156848997127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18846594156656771232664751 28269891234985156848997127)
  ·
    refine ⟨42404836852477735273495691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28269891234985156848997127 42404836852477735273495691)
    ·
      refine ⟨63607255278716602910243537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42404836852477735273495691 63607255278716602910243537)
      ·
        refine ⟨47705441459037452182682653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63607255278716602910243537 47705441459037452182682653)
        ·
          refine ⟨17889540547139044568505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47705441459037452182682653 17889540547139044568505995)
          ·
            refine ⟨26834310820708566852758993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17889540547139044568505995 26834310820708566852758993)
            ·
              refine ⟨20125733115531425139569245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26834310820708566852758993 20125733115531425139569245)
              ·
                refine ⟨7547149918324284427338467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20125733115531425139569245 7547149918324284427338467)
                ·
                  refine ⟨11320724877486426641007701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547149918324284427338467 11320724877486426641007701)
                  ·
                    refine ⟨132664744658044062199309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11320724877486426641007701 132664744658044062199309)
                    ·
                      rfl

theorem cell23_775091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_775091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775091 prefixEnd_775091 := by exact prefixLift 775091
  have htrace : WordTrace (prefixWord ++ tailWord_775091) baseStart_775091 baseEnd_775091 := by
    simpa [prefixWord, tailWord_775091, baseEnd_775091] using wordTrace_append hprefix tailTrace_775091
  have hstable : (prefixWord ++ tailWord_775091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775091).length < 2 ^ (prefixWord ++ tailWord_775091).sum := by decide
  have hdescent : baseEnd_775091 < baseStart_775091 := by decide
  rcases family_descends (prefixWord ++ tailWord_775091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775118 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_775118 : Nat := 118140960795 + 775118 * 2 ^ 59
def prefixEnd_775118 : Nat := 4983230072969 + 3 ^ 40 * 775118 * 2
def baseEnd_775118 : Nat := 398008097951803580960303

theorem tailTrace_775118 : CollatzResearch.WordTrace tailWord_775118 prefixEnd_775118 398008097951803580960303 := by
  unfold tailWord_775118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533859500735917557528751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18847250670591560306820005 3533859500735917557528751)
  ·
    refine ⟨5300789251103876336293127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533859500735917557528751 5300789251103876336293127)
    ·
      refine ⟨7951183876655814504439691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300789251103876336293127 7951183876655814504439691)
      ·
        refine ⟨11926775814983721756659537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951183876655814504439691 11926775814983721756659537)
        ·
          refine ⟨8945081861237791317494653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11926775814983721756659537 8945081861237791317494653)
          ·
            refine ⟨3354405697964171744060495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8945081861237791317494653 3354405697964171744060495)
            ·
              refine ⟨5031608546946257616090743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3354405697964171744060495 5031608546946257616090743)
              ·
                refine ⟨7547412820419386424136115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031608546946257616090743 7547412820419386424136115)
                ·
                  refine ⟨11321119230629079636204173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7547412820419386424136115 11321119230629079636204173)
                  ·
                    refine ⟨4245419711485904863576565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11321119230629079636204173 4245419711485904863576565)
                    ·
                      refine ⟨398008097951803580960303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4245419711485904863576565 398008097951803580960303)
                      ·
                        rfl

theorem cell23_775118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_775118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775118 prefixEnd_775118 := by exact prefixLift 775118
  have htrace : WordTrace (prefixWord ++ tailWord_775118) baseStart_775118 baseEnd_775118 := by
    simpa [prefixWord, tailWord_775118, baseEnd_775118] using wordTrace_append hprefix tailTrace_775118
  have hstable : (prefixWord ++ tailWord_775118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775118).length < 2 ^ (prefixWord ++ tailWord_775118).sum := by decide
  have hdescent : baseEnd_775118 < baseStart_775118 := by decide
  rcases family_descends (prefixWord ++ tailWord_775118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775189 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 5]
def baseStart_775189 : Nat := 118140960795 + 775189 * 2 ^ 59
def prefixEnd_775189 : Nat := 4983230072969 + 3 ^ 40 * 775189 * 2
def baseEnd_775189 : Nat := 44227172786474755908053

theorem tailTrace_775189 : CollatzResearch.WordTrace tailWord_775189 prefixEnd_775189 44227172786474755908053 := by
  unfold tailWord_775189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28273465588630119586064621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18848977059086746390709747 28273465588630119586064621)
  ·
    refine ⟨10602549595736294844774233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28273465588630119586064621 10602549595736294844774233)
    ·
      refine ⟨7951912196802221133580675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10602549595736294844774233 7951912196802221133580675)
      ·
        refine ⟨11927868295203331700371013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7951912196802221133580675 11927868295203331700371013)
        ·
          refine ⟨2236475305350624693819565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11927868295203331700371013 2236475305350624693819565)
          ·
            refine ⟨838678239506484260182337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2236475305350624693819565 838678239506484260182337)
            ·
              refine ⟨629008679629863195136753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 838678239506484260182337 629008679629863195136753)
              ·
                refine ⟨471756509722397396352565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629008679629863195136753 471756509722397396352565)
                ·
                  refine ⟨44227172786474755908053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471756509722397396352565 44227172786474755908053)
                  ·
                    rfl

theorem cell23_775189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_775189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775189 prefixEnd_775189 := by exact prefixLift 775189
  have htrace : WordTrace (prefixWord ++ tailWord_775189) baseStart_775189 baseEnd_775189 := by
    simpa [prefixWord, tailWord_775189, baseEnd_775189] using wordTrace_append hprefix tailTrace_775189
  have hstable : (prefixWord ++ tailWord_775189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775189).length < 2 ^ (prefixWord ++ tailWord_775189).sum := by decide
  have hdescent : baseEnd_775189 < baseStart_775189 := by decide
  rcases family_descends (prefixWord ++ tailWord_775189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775222 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_775222 : Nat := 118140960795 + 775222 * 2 ^ 59
def prefixEnd_775222 : Nat := 4983230072969 + 3 ^ 40 * 775222 * 2
def baseEnd_775222 : Nat := 398061499939871174059825

theorem tailTrace_775222 : CollatzResearch.WordTrace tailWord_775222 prefixEnd_775222 398061499939871174059825 := by
  unfold tailWord_775222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767166824844410388875995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18849779465007044148010613 1767166824844410388875995)
  ·
    refine ⟨2650750237266615583313993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1767166824844410388875995 2650750237266615583313993)
    ·
      refine ⟨1988062677949961687485495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2650750237266615583313993 1988062677949961687485495)
      ·
        refine ⟨2982094016924942531228243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988062677949961687485495 2982094016924942531228243)
        ·
          refine ⟨4473141025387413796842365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982094016924942531228243 4473141025387413796842365)
          ·
            refine ⟨1677427884520280173815887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4473141025387413796842365 1677427884520280173815887)
            ·
              refine ⟨2516141826780420260723831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677427884520280173815887 2516141826780420260723831)
              ·
                refine ⟨3774212740170630391085747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516141826780420260723831 3774212740170630391085747)
                ·
                  refine ⟨5661319110255945586628621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774212740170630391085747 5661319110255945586628621)
                  ·
                    refine ⟨2122994666345979594985733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5661319110255945586628621 2122994666345979594985733)
                    ·
                      refine ⟨398061499939871174059825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2122994666345979594985733 398061499939871174059825)
                      ·
                        rfl

theorem cell23_775222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_775222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775222 prefixEnd_775222 := by exact prefixLift 775222
  have htrace : WordTrace (prefixWord ++ tailWord_775222) baseStart_775222 baseEnd_775222 := by
    simpa [prefixWord, tailWord_775222, baseEnd_775222] using wordTrace_append hprefix tailTrace_775222
  have hstable : (prefixWord ++ tailWord_775222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775222).length < 2 ^ (prefixWord ++ tailWord_775222).sum := by decide
  have hdescent : baseEnd_775222 < baseStart_775222 := by decide
  rcases family_descends (prefixWord ++ tailWord_775222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775258 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_775258 : Nat := 118140960795 + 775258 * 2 ^ 59
def prefixEnd_775258 : Nat := 4983230072969 + 3 ^ 40 * 775258 * 2
def baseEnd_775258 : Nat := 132693328414477677736553

theorem tailTrace_775258 : CollatzResearch.WordTrace tailWord_775258 prefixEnd_775258 132693328414477677736553 := by
  unfold tailWord_775258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068995556345036092581607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18850654816920096246884285 7068995556345036092581607)
  ·
    refine ⟨10603493334517554138872411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068995556345036092581607 10603493334517554138872411)
    ·
      refine ⟨15905240001776331208308617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10603493334517554138872411 15905240001776331208308617)
      ·
        refine ⟨11928930001332248406231463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15905240001776331208308617 11928930001332248406231463)
        ·
          refine ⟨17893395001998372609347195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11928930001332248406231463 17893395001998372609347195)
          ·
            refine ⟨26840092502997558914020793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893395001998372609347195 26840092502997558914020793)
            ·
              refine ⟨20130069377248169185515595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26840092502997558914020793 20130069377248169185515595)
              ·
                refine ⟨30195104065872253778273393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20130069377248169185515595 30195104065872253778273393)
                ·
                  refine ⟨22646328049404190333705045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30195104065872253778273393 22646328049404190333705045)
                  ·
                    refine ⟨132693328414477677736553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 22646328049404190333705045 132693328414477677736553)
                    ·
                      rfl

theorem cell23_775258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_775258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775258 prefixEnd_775258 := by exact prefixLift 775258
  have htrace : WordTrace (prefixWord ++ tailWord_775258) baseStart_775258 baseEnd_775258 := by
    simpa [prefixWord, tailWord_775258, baseEnd_775258] using wordTrace_append hprefix tailTrace_775258
  have hstable : (prefixWord ++ tailWord_775258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775258).length < 2 ^ (prefixWord ++ tailWord_775258).sum := by decide
  have hdescent : baseEnd_775258 < baseStart_775258 := by decide
  rcases family_descends (prefixWord ++ tailWord_775258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775282 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_775282 : Nat := 118140960795 + 775282 * 2 ^ 59
def prefixEnd_775282 : Nat := 4983230072969 + 3 ^ 40 * 775282 * 2
def baseEnd_775282 : Nat := 398092308779140939309549

theorem tailTrace_775282 : CollatzResearch.WordTrace tailWord_775282 prefixEnd_775282 398092308779140939309549 := by
  unfold tailWord_775282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069214394323299117300025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18851238384862130979466733 7069214394323299117300025)
  ·
    refine ⟨5301910795742474337975019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7069214394323299117300025 5301910795742474337975019)
    ·
      refine ⟨7952866193613711506962529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301910795742474337975019 7952866193613711506962529)
      ·
        refine ⟨5964649645210283630221897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7952866193613711506962529 5964649645210283630221897)
        ·
          refine ⟨4473487233907712722666423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5964649645210283630221897 4473487233907712722666423)
          ·
            refine ⟨6710230850861569083999635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473487233907712722666423 6710230850861569083999635)
            ·
              refine ⟨10065346276292353625999453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6710230850861569083999635 10065346276292353625999453)
              ·
                refine ⟨3774504853609632609749795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10065346276292353625999453 3774504853609632609749795)
                ·
                  refine ⟨5661757280414448914624693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774504853609632609749795 5661757280414448914624693)
                  ·
                    refine ⟨530789745038854585746065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5661757280414448914624693 530789745038854585746065)
                    ·
                      refine ⟨398092308779140939309549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530789745038854585746065 398092308779140939309549)
                      ·
                        rfl

theorem cell23_775282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_775282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775282 prefixEnd_775282 := by exact prefixLift 775282
  have htrace : WordTrace (prefixWord ++ tailWord_775282) baseStart_775282 baseEnd_775282 := by
    simpa [prefixWord, tailWord_775282, baseEnd_775282] using wordTrace_append hprefix tailTrace_775282
  have hstable : (prefixWord ++ tailWord_775282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775282).length < 2 ^ (prefixWord ++ tailWord_775282).sum := by decide
  have hdescent : baseEnd_775282 < baseStart_775282 := by decide
  rcases family_descends (prefixWord ++ tailWord_775282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775315 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_775315 : Nat := 118140960795 + 775315 * 2 ^ 59
def prefixEnd_775315 : Nat := 4983230072969 + 3 ^ 40 * 775315 * 2
def baseEnd_775315 : Nat := 398109253640739310196897

theorem tailTrace_775315 : CollatzResearch.WordTrace tailWord_775315 prefixEnd_775315 398109253640739310196897 := by
  unfold tailWord_775315
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278061186173643105151399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18852040790782428736767599 28278061186173643105151399)
  ·
    refine ⟨42417091779260464657727099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28278061186173643105151399 42417091779260464657727099)
    ·
      refine ⟨63625637668890696986590649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42417091779260464657727099 63625637668890696986590649)
      ·
        refine ⟨47719228251668022739942987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63625637668890696986590649 47719228251668022739942987)
        ·
          refine ⟨71578842377502034109914481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47719228251668022739942987 71578842377502034109914481)
          ·
            refine ⟨53684131783126525582435861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71578842377502034109914481 53684131783126525582435861)
            ·
              refine ⟨2516443677334055886676681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53684131783126525582435861 2516443677334055886676681)
              ·
                refine ⟨1887332758000541915007511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516443677334055886676681 1887332758000541915007511)
                ·
                  refine ⟨2830999137000812872511267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887332758000541915007511 2830999137000812872511267)
                  ·
                    refine ⟨4246498705501219308766901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2830999137000812872511267 4246498705501219308766901)
                    ·
                      refine ⟨398109253640739310196897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4246498705501219308766901 398109253640739310196897)
                      ·
                        rfl

theorem cell23_775315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_775315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775315 prefixEnd_775315 := by exact prefixLift 775315
  have htrace : WordTrace (prefixWord ++ tailWord_775315) baseStart_775315 baseEnd_775315 := by
    simpa [prefixWord, tailWord_775315, baseEnd_775315] using wordTrace_append hprefix tailTrace_775315
  have hstable : (prefixWord ++ tailWord_775315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775315).length < 2 ^ (prefixWord ++ tailWord_775315).sum := by decide
  have hdescent : baseEnd_775315 < baseStart_775315 := by decide
  rcases family_descends (prefixWord ++ tailWord_775315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775325 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_775325 : Nat := 118140960795 + 775325 * 2 ^ 59
def prefixEnd_775325 : Nat := 4983230072969 + 3 ^ 40 * 775325 * 2
def baseEnd_775325 : Nat := 398114388447284271071851

theorem tailTrace_775325 : CollatzResearch.WordTrace tailWord_775325 prefixEnd_775325 398114388447284271071851 := by
  unfold tailWord_775325
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278425916137414813015429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18852283944091609875343619 28278425916137414813015429)
  ·
    refine ⟨5302204859275765277440393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28278425916137414813015429 5302204859275765277440393)
    ·
      refine ⟨3976653644456823958080295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5302204859275765277440393 3976653644456823958080295)
      ·
        refine ⟨5964980466685235937120443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3976653644456823958080295 5964980466685235937120443)
        ·
          refine ⟨8947470700027853905680665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5964980466685235937120443 8947470700027853905680665)
          ·
            refine ⟨6710603025020890429260499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8947470700027853905680665 6710603025020890429260499)
            ·
              refine ⟨10065904537531335643890749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6710603025020890429260499 10065904537531335643890749)
              ·
                refine ⟨3774714201574250866459031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10065904537531335643890749 3774714201574250866459031)
                ·
                  refine ⟨5662071302361376299688547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3774714201574250866459031 5662071302361376299688547)
                  ·
                    refine ⟨8493106953542064449532821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5662071302361376299688547 8493106953542064449532821)
                    ·
                      refine ⟨398114388447284271071851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8493106953542064449532821 398114388447284271071851)
                      ·
                        rfl

theorem cell23_775325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_775325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775325 prefixEnd_775325 := by exact prefixLift 775325
  have htrace : WordTrace (prefixWord ++ tailWord_775325) baseStart_775325 baseEnd_775325 := by
    simpa [prefixWord, tailWord_775325, baseEnd_775325] using wordTrace_append hprefix tailTrace_775325
  have hstable : (prefixWord ++ tailWord_775325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775325).length < 2 ^ (prefixWord ++ tailWord_775325).sum := by decide
  have hdescent : baseEnd_775325 < baseStart_775325 := by decide
  rcases family_descends (prefixWord ++ tailWord_775325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775326 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_775326 : Nat := 118140960795 + 775326 * 2 ^ 59
def prefixEnd_775326 : Nat := 4983230072969 + 3 ^ 40 * 775326 * 2
def baseEnd_775326 : Nat := 132704967309312922386449

theorem tailTrace_775326 : CollatzResearch.WordTrace tailWord_775326 prefixEnd_775326 132704967309312922386449 := by
  unfold tailWord_775326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534807798641723997975229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18852308259422527989201221 3534807798641723997975229)
  ·
    refine ⟨1325552924490646499240711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3534807798641723997975229 1325552924490646499240711)
    ·
      refine ⟨1988329386735969748861067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325552924490646499240711 1988329386735969748861067)
      ·
        refine ⟨2982494080103954623291601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988329386735969748861067 2982494080103954623291601)
        ·
          refine ⟨2236870560077965967468701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2982494080103954623291601 2236870560077965967468701)
          ·
            refine ⟨838826460029237237800763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2236870560077965967468701 838826460029237237800763)
            ·
              refine ⟨1258239690043855856701145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838826460029237237800763 1258239690043855856701145)
              ·
                refine ⟨943679767532891892525859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258239690043855856701145 943679767532891892525859)
                ·
                  refine ⟨1415519651299337838788789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943679767532891892525859 1415519651299337838788789)
                  ·
                    refine ⟨132704967309312922386449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1415519651299337838788789 132704967309312922386449)
                    ·
                      rfl

theorem cell23_775326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_775326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775326 prefixEnd_775326 := by exact prefixLift 775326
  have htrace : WordTrace (prefixWord ++ tailWord_775326) baseStart_775326 baseEnd_775326 := by
    simpa [prefixWord, tailWord_775326, baseEnd_775326] using wordTrace_append hprefix tailTrace_775326
  have hstable : (prefixWord ++ tailWord_775326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775326).length < 2 ^ (prefixWord ++ tailWord_775326).sum := by decide
  have hdescent : baseEnd_775326 < baseStart_775326 := by decide
  rcases family_descends (prefixWord ++ tailWord_775326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775329 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_775329 : Nat := 118140960795 + 775329 * 2 ^ 59
def prefixEnd_775329 : Nat := 4983230072969 + 3 ^ 40 * 775329 * 2
def baseEnd_775329 : Nat := 398116442369902255421833

theorem tailTrace_775329 : CollatzResearch.WordTrace tailWord_775329 prefixEnd_775329 398116442369902255421833 := by
  unfold tailWord_775329
  simp only [CollatzResearch.WordTrace]
  refine ⟨28278571808122923496161041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18852381205415282330774027 28278571808122923496161041)
  ·
    refine ⟨21208928856092192622120781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28278571808122923496161041 21208928856092192622120781)
    ·
      refine ⟨7953348321034572233295293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21208928856092192622120781 7953348321034572233295293)
      ·
        refine ⟨2982505620387964587485735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7953348321034572233295293 2982505620387964587485735)
        ·
          refine ⟨4473758430581946881228603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982505620387964587485735 4473758430581946881228603)
          ·
            refine ⟨6710637645872920321842905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473758430581946881228603 6710637645872920321842905)
            ·
              refine ⟨5032978234404690241382179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6710637645872920321842905 5032978234404690241382179)
              ·
                refine ⟨7549467351607035362073269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032978234404690241382179 7549467351607035362073269)
                ·
                  refine ⟨707762564213159565194369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7549467351607035362073269 707762564213159565194369)
                  ·
                    refine ⟨530821923159869673895777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 707762564213159565194369 530821923159869673895777)
                    ·
                      refine ⟨398116442369902255421833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530821923159869673895777 398116442369902255421833)
                      ·
                        rfl

theorem cell23_775329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_775329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775329 prefixEnd_775329 := by exact prefixLift 775329
  have htrace : WordTrace (prefixWord ++ tailWord_775329) baseStart_775329 baseEnd_775329 := by
    simpa [prefixWord, tailWord_775329, baseEnd_775329] using wordTrace_append hprefix tailTrace_775329
  have hstable : (prefixWord ++ tailWord_775329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775329).length < 2 ^ (prefixWord ++ tailWord_775329).sum := by decide
  have hdescent : baseEnd_775329 < baseStart_775329 := by decide
  rcases family_descends (prefixWord ++ tailWord_775329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775385 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 4]
def baseStart_775385 : Nat := 118140960795 + 775385 * 2 ^ 59
def prefixEnd_775385 : Nat := 4983230072969 + 3 ^ 40 * 775385 * 2
def baseEnd_775385 : Nat := 398145197286554036321575

theorem tailTrace_775385 : CollatzResearch.WordTrace tailWord_775385 prefixEnd_775385 398145197286554036321575 := by
  unfold tailWord_775385
  simp only [CollatzResearch.WordTrace]
  refine ⟨28280614295920045060199609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18853742863946696706799739 28280614295920045060199609)
  ·
    refine ⟨21210460721940033795149707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28280614295920045060199609 21210460721940033795149707)
    ·
      refine ⟨31815691082910050692724561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21210460721940033795149707 31815691082910050692724561)
      ·
        refine ⟨23861768312182538019543421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31815691082910050692724561 23861768312182538019543421)
        ·
          refine ⟨8948163117068451757328783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23861768312182538019543421 8948163117068451757328783)
          ·
            refine ⟨13422244675602677635993175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948163117068451757328783 13422244675602677635993175)
            ·
              refine ⟨20133367013404016453989763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13422244675602677635993175 20133367013404016453989763)
              ·
                refine ⟨30200050520106024680984645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20133367013404016453989763 30200050520106024680984645)
                ·
                  refine ⟨5662509472519879627684621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30200050520106024680984645 5662509472519879627684621)
                  ·
                    refine ⟨2123441052194954860381733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5662509472519879627684621 2123441052194954860381733)
                    ·
                      refine ⟨398145197286554036321575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2123441052194954860381733 398145197286554036321575)
                      ·
                        rfl

theorem cell23_775385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_775385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775385 prefixEnd_775385 := by exact prefixLift 775385
  have htrace : WordTrace (prefixWord ++ tailWord_775385) baseStart_775385 baseEnd_775385 := by
    simpa [prefixWord, tailWord_775385, baseEnd_775385] using wordTrace_append hprefix tailTrace_775385
  have hstable : (prefixWord ++ tailWord_775385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775385).length < 2 ^ (prefixWord ++ tailWord_775385).sum := by decide
  have hdescent : baseEnd_775385 < baseStart_775385 := by decide
  rcases family_descends (prefixWord ++ tailWord_775385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775415 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_775415 : Nat := 118140960795 + 775415 * 2 ^ 59
def prefixEnd_775415 : Nat := 4983230072969 + 3 ^ 40 * 775415 * 2
def baseEnd_775415 : Nat := 398160601706188918946437

theorem tailTrace_775415 : CollatzResearch.WordTrace tailWord_775415 prefixEnd_775415 398160601706188918946437 := by
  unfold tailWord_775415
  simp only [CollatzResearch.WordTrace]
  refine ⟨28281708485811360183791699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18854472323874240122527799 28281708485811360183791699)
  ·
    refine ⟨42422562728717040275687549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28281708485811360183791699 42422562728717040275687549)
    ·
      refine ⟨15908461023268890103382831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42422562728717040275687549 15908461023268890103382831)
      ·
        refine ⟨23862691534903335155074247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15908461023268890103382831 23862691534903335155074247)
        ·
          refine ⟨35794037302355002732611371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23862691534903335155074247 35794037302355002732611371)
          ·
            refine ⟨53691055953532504098917057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35794037302355002732611371 53691055953532504098917057)
            ·
              refine ⟨40268291965149378074187793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53691055953532504098917057 40268291965149378074187793)
              ·
                refine ⟨30201218973862033555640845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40268291965149378074187793 30201218973862033555640845)
                ·
                  refine ⟨11325457115198262583365317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30201218973862033555640845 11325457115198262583365317)
                  ·
                    refine ⟨2123523209099674234380997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11325457115198262583365317 2123523209099674234380997)
                    ·
                      refine ⟨398160601706188918946437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2123523209099674234380997 398160601706188918946437)
                      ·
                        rfl

theorem cell23_775415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_775415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775415 prefixEnd_775415 := by exact prefixLift 775415
  have htrace : WordTrace (prefixWord ++ tailWord_775415) baseStart_775415 baseEnd_775415 := by
    simpa [prefixWord, tailWord_775415, baseEnd_775415] using wordTrace_append hprefix tailTrace_775415
  have hstable : (prefixWord ++ tailWord_775415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775415).length < 2 ^ (prefixWord ++ tailWord_775415).sum := by decide
  have hdescent : baseEnd_775415 < baseStart_775415 := by decide
  rcases family_descends (prefixWord ++ tailWord_775415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775436 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_775436 : Nat := 118140960795 + 775436 * 2 ^ 59
def prefixEnd_775436 : Nat := 4983230072969 + 3 ^ 40 * 775436 * 2
def baseEnd_775436 : Nat := 398171384799933336783841

theorem tailTrace_775436 : CollatzResearch.WordTrace tailWord_775436 prefixEnd_775436 398171384799933336783841 := by
  unfold tailWord_775436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141237209367640385153081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18854982945823520513537441 14141237209367640385153081)
  ·
    refine ⟨10605927907025730288864811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14141237209367640385153081 10605927907025730288864811)
    ·
      refine ⟨15908891860538595433297217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10605927907025730288864811 15908891860538595433297217)
      ·
        refine ⟨11931668895403946574972913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15908891860538595433297217 11931668895403946574972913)
        ·
          refine ⟨8948751671552959931229685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11931668895403946574972913 8948751671552959931229685)
          ·
            refine ⟨838945469208089993552783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8948751671552959931229685 838945469208089993552783)
            ·
              refine ⟨1258418203812134990329175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 838945469208089993552783 1258418203812134990329175)
              ·
                refine ⟨1887627305718202485493763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258418203812134990329175 1887627305718202485493763)
                ·
                  refine ⟨2831440958577303728240645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887627305718202485493763 2831440958577303728240645)
                  ·
                    refine ⟨530895179733244449045121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831440958577303728240645 530895179733244449045121)
                    ·
                      refine ⟨398171384799933336783841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530895179733244449045121 398171384799933336783841)
                      ·
                        rfl

theorem cell23_775436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_775436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775436 prefixEnd_775436 := by exact prefixLift 775436
  have htrace : WordTrace (prefixWord ++ tailWord_775436) baseStart_775436 baseEnd_775436 := by
    simpa [prefixWord, tailWord_775436, baseEnd_775436] using wordTrace_append hprefix tailTrace_775436
  have hstable : (prefixWord ++ tailWord_775436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775436).length < 2 ^ (prefixWord ++ tailWord_775436).sum := by decide
  have hdescent : baseEnd_775436 < baseStart_775436 := by decide
  rcases family_descends (prefixWord ++ tailWord_775436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775452 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_775452 : Nat := 118140960795 + 775452 * 2 ^ 59
def prefixEnd_775452 : Nat := 4983230072969 + 3 ^ 40 * 775452 * 2
def baseEnd_775452 : Nat := 398179600490405274183767

theorem tailTrace_775452 : CollatzResearch.WordTrace tailWord_775452 prefixEnd_775452 398179600490405274183767 := by
  unfold tailWord_775452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141528993338657751444305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18855371991118210335259073 14141528993338657751444305)
  ·
    refine ⟨10606146745003993313583229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14141528993338657751444305 10606146745003993313583229)
    ·
      refine ⟨3977305029376497492593711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10606146745003993313583229 3977305029376497492593711)
      ·
        refine ⟨5965957544064746238890567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977305029376497492593711 5965957544064746238890567)
        ·
          refine ⟨8948936316097119358335851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5965957544064746238890567 8948936316097119358335851)
          ·
            refine ⟨13423404474145679037503777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8948936316097119358335851 13423404474145679037503777)
            ·
              refine ⟨10067553355609259278127833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13423404474145679037503777 10067553355609259278127833)
              ·
                refine ⟨7550665016706944458595875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10067553355609259278127833 7550665016706944458595875)
                ·
                  refine ⟨11325997525060416687893813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7550665016706944458595875 11325997525060416687893813)
                  ·
                    refine ⟨1061812267974414064490045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11325997525060416687893813 1061812267974414064490045)
                    ·
                      refine ⟨398179600490405274183767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1061812267974414064490045 398179600490405274183767)
                      ·
                        rfl

theorem cell23_775452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_775452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775452 prefixEnd_775452 := by exact prefixLift 775452
  have htrace : WordTrace (prefixWord ++ tailWord_775452) baseStart_775452 baseEnd_775452 := by
    simpa [prefixWord, tailWord_775452, baseEnd_775452] using wordTrace_append hprefix tailTrace_775452
  have hstable : (prefixWord ++ tailWord_775452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775452).length < 2 ^ (prefixWord ++ tailWord_775452).sum := by decide
  have hdescent : baseEnd_775452 < baseStart_775452 := by decide
  rcases family_descends (prefixWord ++ tailWord_775452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775459 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 5]
def baseStart_775459 : Nat := 118140960795 + 775459 * 2 ^ 59
def prefixEnd_775459 : Nat := 4983230072969 + 3 ^ 40 * 775459 * 2
def baseEnd_775459 : Nat := 44242577206109638532915

theorem tailTrace_775459 : CollatzResearch.WordTrace tailWord_775459 prefixEnd_775459 44242577206109638532915 := by
  unfold tailWord_775459
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283313297651955698393431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18855542198434637132262287 28283313297651955698393431)
  ·
    refine ⟨42424969946477933547590147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28283313297651955698393431 42424969946477933547590147)
    ·
      refine ⟨63637454919716900321385221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42424969946477933547590147 63637454919716900321385221)
      ·
        refine ⟨11932022797446918810259729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63637454919716900321385221 11932022797446918810259729)
        ·
          refine ⟨8949017098085189107694797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11932022797446918810259729 8949017098085189107694797)
          ·
            refine ⟨3355881411781945915385549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8949017098085189107694797 3355881411781945915385549)
            ·
              refine ⟨1258455529418229718269581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3355881411781945915385549 1258455529418229718269581)
              ·
                refine ⟨471920823531836144351093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258455529418229718269581 471920823531836144351093)
                ·
                  refine ⟨44242577206109638532915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 471920823531836144351093 44242577206109638532915)
                  ·
                    rfl

theorem cell23_775459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 5].length) (baseStart_775459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775459 prefixEnd_775459 := by exact prefixLift 775459
  have htrace : WordTrace (prefixWord ++ tailWord_775459) baseStart_775459 baseEnd_775459 := by
    simpa [prefixWord, tailWord_775459, baseEnd_775459] using wordTrace_append hprefix tailTrace_775459
  have hstable : (prefixWord ++ tailWord_775459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775459).length < 2 ^ (prefixWord ++ tailWord_775459).sum := by decide
  have hdescent : baseEnd_775459 < baseStart_775459 := by decide
  rcases family_descends (prefixWord ++ tailWord_775459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 5]
def baseStart_775465 : Nat := 118140960795 + 775465 * 2 ^ 59
def prefixEnd_775465 : Nat := 4983230072969 + 3 ^ 40 * 775465 * 2
def baseEnd_775465 : Nat := 398186275738913723321207

theorem tailTrace_775465 : CollatzResearch.WordTrace tailWord_775465 prefixEnd_775465 398186275738913723321207 := by
  unfold tailWord_775465
  simp only [CollatzResearch.WordTrace]
  refine ⟨28283532135630218723111849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18855688090420145815407899 28283532135630218723111849)
  ·
    refine ⟨21212649101722664042333887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28283532135630218723111849 21212649101722664042333887)
    ·
      refine ⟨31818973652583996063500831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21212649101722664042333887 31818973652583996063500831)
      ·
        refine ⟨47728460478875994095251247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31818973652583996063500831 47728460478875994095251247)
        ·
          refine ⟨71592690718313991142876871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47728460478875994095251247 71592690718313991142876871)
          ·
            refine ⟨107389036077470986714315307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71592690718313991142876871 107389036077470986714315307)
            ·
              refine ⟨161083554116206480071472961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107389036077470986714315307 161083554116206480071472961)
              ·
                refine ⟨120812665587154860053604721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161083554116206480071472961 120812665587154860053604721)
                ·
                  refine ⟨90609499190366145040203541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120812665587154860053604721 90609499190366145040203541)
                  ·
                    refine ⟨4247320274548413048759541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90609499190366145040203541 4247320274548413048759541)
                    ·
                      refine ⟨398186275738913723321207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4247320274548413048759541 398186275738913723321207)
                      ·
                        rfl

theorem cell23_775465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_775465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775465 prefixEnd_775465 := by exact prefixLift 775465
  have htrace : WordTrace (prefixWord ++ tailWord_775465) baseStart_775465 baseEnd_775465 := by
    simpa [prefixWord, tailWord_775465, baseEnd_775465] using wordTrace_append hprefix tailTrace_775465
  have hstable : (prefixWord ++ tailWord_775465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775465).length < 2 ^ (prefixWord ++ tailWord_775465).sum := by decide
  have hdescent : baseEnd_775465 < baseStart_775465 := by decide
  rcases family_descends (prefixWord ++ tailWord_775465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775472 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_775472 : Nat := 118140960795 + 775472 * 2 ^ 59
def prefixEnd_775472 : Nat := 4983230072969 + 3 ^ 40 * 775472 * 2
def baseEnd_775472 : Nat := 132729956701165065311225

theorem tailTrace_775472 : CollatzResearch.WordTrace tailWord_775472 prefixEnd_775472 132729956701165065311225 := by
  unfold tailWord_775472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141893723302429459308335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18855858297736572612411113 14141893723302429459308335)
  ·
    refine ⟨21212840584953644188962503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14141893723302429459308335 21212840584953644188962503)
    ·
      refine ⟨31819260877430466283443755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21212840584953644188962503 31819260877430466283443755)
      ·
        refine ⟨47728891316145699425165633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31819260877430466283443755 47728891316145699425165633)
        ·
          refine ⟨35796668487109274568874225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47728891316145699425165633 35796668487109274568874225)
          ·
            refine ⟨26847501365331955926655669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35796668487109274568874225 26847501365331955926655669)
            ·
              refine ⟨2516953252999870868123969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26847501365331955926655669 2516953252999870868123969)
              ·
                refine ⟨1887714939749903151092977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516953252999870868123969 1887714939749903151092977)
                ·
                  refine ⟨1415786204812427363319733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887714939749903151092977 1415786204812427363319733)
                  ·
                    refine ⟨132729956701165065311225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1415786204812427363319733 132729956701165065311225)
                    ·
                      rfl

theorem cell23_775472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_775472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775472 prefixEnd_775472 := by exact prefixLift 775472
  have htrace : WordTrace (prefixWord ++ tailWord_775472) baseStart_775472 baseEnd_775472 := by
    simpa [prefixWord, tailWord_775472, baseEnd_775472] using wordTrace_append hprefix tailTrace_775472
  have hstable : (prefixWord ++ tailWord_775472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775472).length < 2 ^ (prefixWord ++ tailWord_775472).sum := by decide
  have hdescent : baseEnd_775472 < baseStart_775472 := by decide
  rcases family_descends (prefixWord ++ tailWord_775472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775482 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_775482 : Nat := 118140960795 + 775482 * 2 ^ 59
def prefixEnd_775482 : Nat := 4983230072969 + 3 ^ 40 * 775482 * 2
def baseEnd_775482 : Nat := 398195004910040156808629

theorem tailTrace_775482 : CollatzResearch.WordTrace tailWord_775482 prefixEnd_775482 398195004910040156808629 := by
  unfold tailWord_775482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071038044142157656620175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18856101451045753750987133 7071038044142157656620175)
  ·
    refine ⟨10606557066213236484930263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7071038044142157656620175 10606557066213236484930263)
    ·
      refine ⟨15909835599319854727395395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10606557066213236484930263 15909835599319854727395395)
      ·
        refine ⟨23864753398979782091093093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15909835599319854727395395 23864753398979782091093093)
        ·
          refine ⟨4474641262308709142079955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23864753398979782091093093 4474641262308709142079955)
          ·
            refine ⟨6711961893463063713119933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4474641262308709142079955 6711961893463063713119933)
            ·
              refine ⟨2516985710048648892419975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6711961893463063713119933 2516985710048648892419975)
              ·
                refine ⟨3775478565072973338629963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516985710048648892419975 3775478565072973338629963)
                ·
                  refine ⟨5663217847609460007944945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775478565072973338629963 5663217847609460007944945)
                  ·
                    refine ⟨4247413385707095005958709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5663217847609460007944945 4247413385707095005958709)
                    ·
                      refine ⟨398195004910040156808629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4247413385707095005958709 398195004910040156808629)
                      ·
                        rfl

theorem cell23_775482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_775482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775482 prefixEnd_775482 := by exact prefixLift 775482
  have htrace : WordTrace (prefixWord ++ tailWord_775482) baseStart_775482 baseEnd_775482 := by
    simpa [prefixWord, tailWord_775482, baseEnd_775482] using wordTrace_append hprefix tailTrace_775482
  have hstable : (prefixWord ++ tailWord_775482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775482).length < 2 ^ (prefixWord ++ tailWord_775482).sum := by decide
  have hdescent : baseEnd_775482 < baseStart_775482 := by decide
  rcases family_descends (prefixWord ++ tailWord_775482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775509 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_775509 : Nat := 118140960795 + 775509 * 2 ^ 59
def prefixEnd_775509 : Nat := 4983230072969 + 3 ^ 40 * 775509 * 2
def baseEnd_775509 : Nat := 398208868887711551171005

theorem tailTrace_775509 : CollatzResearch.WordTrace tailWord_775509 prefixEnd_775509 398208868887711551171005 := by
  unfold tailWord_775509
  simp only [CollatzResearch.WordTrace]
  refine ⟨28285136947470814237713581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18856757964980542825142387 28285136947470814237713581)
  ·
    refine ⟨10606926355301555339142593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28285136947470814237713581 10606926355301555339142593)
    ·
      refine ⟨7955194766476166504356945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10606926355301555339142593 7955194766476166504356945)
      ·
        refine ⟨5966396074857124878267709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7955194766476166504356945 5966396074857124878267709)
        ·
          refine ⟨2237398528071421829350391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5966396074857124878267709 2237398528071421829350391)
          ·
            refine ⟨3356097792107132744025587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237398528071421829350391 3356097792107132744025587)
            ·
              refine ⟨5034146688160699116038381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3356097792107132744025587 5034146688160699116038381)
              ·
                refine ⟨1887805008060262168514393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5034146688160699116038381 1887805008060262168514393)
                ·
                  refine ⟨1415853756045196626385795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887805008060262168514393 1415853756045196626385795)
                  ·
                    refine ⟨2123780634067794939578693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1415853756045196626385795 2123780634067794939578693)
                    ·
                      refine ⟨398208868887711551171005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2123780634067794939578693 398208868887711551171005)
                      ·
                        rfl

theorem cell23_775509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_775509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775509 prefixEnd_775509 := by exact prefixLift 775509
  have htrace : WordTrace (prefixWord ++ tailWord_775509) baseStart_775509 baseEnd_775509 := by
    simpa [prefixWord, tailWord_775509, baseEnd_775509] using wordTrace_append hprefix tailTrace_775509
  have hstable : (prefixWord ++ tailWord_775509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775509).length < 2 ^ (prefixWord ++ tailWord_775509).sum := by decide
  have hdescent : baseEnd_775509 < baseStart_775509 := by decide
  rcases family_descends (prefixWord ++ tailWord_775509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775536 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 1, 4]
def baseStart_775536 : Nat := 118140960795 + 775536 * 2 ^ 59
def prefixEnd_775536 : Nat := 4983230072969 + 3 ^ 40 * 775536 * 2
def baseEnd_775536 : Nat := 132740910955127648511127

theorem tailTrace_775536 : CollatzResearch.WordTrace tailWord_775536 prefixEnd_775536 132740910955127648511127 := by
  unfold tailWord_775536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143060859186498924473231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18857414478915331899297641 14143060859186498924473231)
  ·
    refine ⟨21214591288779748386709847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143060859186498924473231 21214591288779748386709847)
    ·
      refine ⟨31821886933169622580064771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21214591288779748386709847 31821886933169622580064771)
      ·
        refine ⟨47732830399754433870097157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31821886933169622580064771 47732830399754433870097157)
        ·
          refine ⟨8949905699953956350643217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47732830399754433870097157 8949905699953956350643217)
          ·
            refine ⟨6712429274965467262982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8949905699953956350643217 6712429274965467262982413)
            ·
              refine ⟨2517160978112050223618405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6712429274965467262982413 2517160978112050223618405)
              ·
                refine ⟨471967683396009416928451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2517160978112050223618405 471967683396009416928451)
                ·
                  refine ⟨707951525094014125392677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471967683396009416928451 707951525094014125392677)
                  ·
                    refine ⟨132740910955127648511127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707951525094014125392677 132740910955127648511127)
                    ·
                      rfl

theorem cell23_775536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 1, 4].length) (baseStart_775536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775536 prefixEnd_775536 := by exact prefixLift 775536
  have htrace : WordTrace (prefixWord ++ tailWord_775536) baseStart_775536 baseEnd_775536 := by
    simpa [prefixWord, tailWord_775536, baseEnd_775536] using wordTrace_append hprefix tailTrace_775536
  have hstable : (prefixWord ++ tailWord_775536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775536).length < 2 ^ (prefixWord ++ tailWord_775536).sum := by decide
  have hdescent : baseEnd_775536 < baseStart_775536 := by decide
  rcases family_descends (prefixWord ++ tailWord_775536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775569 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 5, 2]
def baseStart_775569 : Nat := 118140960795 + 775569 * 2 ^ 59
def prefixEnd_775569 : Nat := 4983230072969 + 3 ^ 40 * 775569 * 2
def baseEnd_775569 : Nat := 398239677726981316420729

theorem tailTrace_775569 : CollatzResearch.WordTrace tailWord_775569 prefixEnd_775569 398239677726981316420729 := by
  unfold tailWord_775569
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287325327253444484897761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18858216884835629656598507 28287325327253444484897761)
  ·
    refine ⟨21215493995440083363673321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28287325327253444484897761 21215493995440083363673321)
    ·
      refine ⟨15911620496580062522754991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21215493995440083363673321 15911620496580062522754991)
      ·
        refine ⟨23867430744870093784132487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15911620496580062522754991 23867430744870093784132487)
        ·
          refine ⟨35801146117305140676198731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23867430744870093784132487 35801146117305140676198731)
          ·
            refine ⟨53701719175957711014298097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35801146117305140676198731 53701719175957711014298097)
            ·
              refine ⟨40276289381968283260723573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53701719175957711014298097 40276289381968283260723573)
              ·
                refine ⟨3775902129559526555692835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40276289381968283260723573 3775902129559526555692835)
                ·
                  refine ⟨5663853194339289833539253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775902129559526555692835 5663853194339289833539253)
                  ·
                    refine ⟨530986236969308421894305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5663853194339289833539253 530986236969308421894305)
                    ·
                      refine ⟨398239677726981316420729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 530986236969308421894305 398239677726981316420729)
                      ·
                        rfl

theorem cell23_775569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_775569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775569 prefixEnd_775569 := by exact prefixLift 775569
  have htrace : WordTrace (prefixWord ++ tailWord_775569) baseStart_775569 baseEnd_775569 := by
    simpa [prefixWord, tailWord_775569, baseEnd_775569] using wordTrace_append hprefix tailTrace_775569
  have hstable : (prefixWord ++ tailWord_775569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775569).length < 2 ^ (prefixWord ++ tailWord_775569).sum := by decide
  have hdescent : baseEnd_775569 < baseStart_775569 := by decide
  rcases family_descends (prefixWord ++ tailWord_775569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775619 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3]
def baseStart_775619 : Nat := 118140960795 + 775619 * 2 ^ 59
def prefixEnd_775619 : Nat := 4983230072969 + 3 ^ 40 * 775619 * 2
def baseEnd_775619 : Nat := 398265351759706120795499

theorem tailTrace_775619 : CollatzResearch.WordTrace tailWord_775619 prefixEnd_775619 398265351759706120795499 := by
  unfold tailWord_775619
  simp only [CollatzResearch.WordTrace]
  refine ⟨28289148977072303024217911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18859432651381535349478607 28289148977072303024217911)
  ·
    refine ⟨42433723465608454536326867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28289148977072303024217911 42433723465608454536326867)
    ·
      refine ⟨63650585198412681804490301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42433723465608454536326867 63650585198412681804490301)
      ·
        refine ⟨23868969449404755676683863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63650585198412681804490301 23868969449404755676683863)
        ·
          refine ⟨35803454174107133515025795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23868969449404755676683863 35803454174107133515025795)
          ·
            refine ⟨53705181261160700272538693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35803454174107133515025795 53705181261160700272538693)
            ·
              refine ⟨10069721486467631301101005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53705181261160700272538693 10069721486467631301101005)
              ·
                refine ⟨3776145557425361737912877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10069721486467631301101005 3776145557425361737912877)
                ·
                  refine ⟨1416054584034510651717329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3776145557425361737912877 1416054584034510651717329)
                  ·
                    refine ⟨1062040938025882988787997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416054584034510651717329 1062040938025882988787997)
                    ·
                      refine ⟨398265351759706120795499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062040938025882988787997 398265351759706120795499)
                      ·
                        rfl

theorem cell23_775619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_775619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775619 prefixEnd_775619 := by exact prefixLift 775619
  have htrace : WordTrace (prefixWord ++ tailWord_775619) baseStart_775619 baseEnd_775619 := by
    simpa [prefixWord, tailWord_775619, baseEnd_775619] using wordTrace_append hprefix tailTrace_775619
  have hstable : (prefixWord ++ tailWord_775619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775619).length < 2 ^ (prefixWord ++ tailWord_775619).sum := by decide
  have hdescent : baseEnd_775619 < baseStart_775619 := by decide
  rcases family_descends (prefixWord ++ tailWord_775619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775670 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3]
def baseStart_775670 : Nat := 118140960795 + 775670 * 2 ^ 59
def prefixEnd_775670 : Nat := 4983230072969 + 3 ^ 40 * 775670 * 2
def baseEnd_775670 : Nat := 398291539273085421257765

theorem tailTrace_775670 : CollatzResearch.WordTrace tailWord_775670 prefixEnd_775670 398291539273085421257765 := by
  unfold tailWord_775670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768188068742971170895279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18860672733258359156216309 1768188068742971170895279)
  ·
    refine ⟨2652282103114456756342919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768188068742971170895279 2652282103114456756342919)
    ·
      refine ⟨3978423154671685134514379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652282103114456756342919 3978423154671685134514379)
      ·
        refine ⟨5967634732007527701771569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3978423154671685134514379 5967634732007527701771569)
        ·
          refine ⟨4475726049005645776328677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5967634732007527701771569 4475726049005645776328677)
          ·
            refine ⟨839198634188558583061627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4475726049005645776328677 839198634188558583061627)
            ·
              refine ⟨1258797951282837874592441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839198634188558583061627 1258797951282837874592441)
              ·
                refine ⟨944098463462128405944331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258797951282837874592441 944098463462128405944331)
                ·
                  refine ⟨1416147695193192608916497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944098463462128405944331 1416147695193192608916497)
                  ·
                    refine ⟨1062110771394894456687373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1416147695193192608916497 1062110771394894456687373)
                    ·
                      refine ⟨398291539273085421257765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062110771394894456687373 398291539273085421257765)
                      ·
                        rfl

theorem cell23_775670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_775670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775670 prefixEnd_775670 := by exact prefixLift 775670
  have htrace : WordTrace (prefixWord ++ tailWord_775670) baseStart_775670 baseEnd_775670 := by
    simpa [prefixWord, tailWord_775670, baseEnd_775670] using wordTrace_append hprefix tailTrace_775670
  have hstable : (prefixWord ++ tailWord_775670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775670).length < 2 ^ (prefixWord ++ tailWord_775670).sum := by decide
  have hdescent : baseEnd_775670 < baseStart_775670 := by decide
  rcases family_descends (prefixWord ++ tailWord_775670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775706 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2]
def baseStart_775706 : Nat := 118140960795 + 775706 * 2 ^ 59
def prefixEnd_775706 : Nat := 4983230072969 + 3 ^ 40 * 775706 * 2
def baseEnd_775706 : Nat := 398310024576647280407599

theorem tailTrace_775706 : CollatzResearch.WordTrace tailWord_775706 prefixEnd_775706 398310024576647280407599 := by
  unfold tailWord_775706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073080531939279220658743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18861548085171411255089981 7073080531939279220658743)
  ·
    refine ⟨10609620797908918830988115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7073080531939279220658743 10609620797908918830988115)
    ·
      refine ⟨15914431196863378246482173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609620797908918830988115 15914431196863378246482173)
      ·
        refine ⟨5967911698823766842430815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15914431196863378246482173 5967911698823766842430815)
        ·
          refine ⟨8951867548235650263646223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5967911698823766842430815 8951867548235650263646223)
          ·
            refine ⟨13427801322353475395469335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8951867548235650263646223 13427801322353475395469335)
            ·
              refine ⟨20141701983530213093204003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13427801322353475395469335 20141701983530213093204003)
              ·
                refine ⟨30212552975295319639806005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20141701983530213093204003 30212552975295319639806005)
                ·
                  refine ⟨2832426841433936216231813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30212552975295319639806005 2832426841433936216231813)
                  ·
                    refine ⟨531080032768863040543465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832426841433936216231813 531080032768863040543465)
                    ·
                      refine ⟨398310024576647280407599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531080032768863040543465 398310024576647280407599)
                      ·
                        rfl

theorem cell23_775706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_775706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775706 prefixEnd_775706 := by exact prefixLift 775706
  have htrace : WordTrace (prefixWord ++ tailWord_775706) baseStart_775706 baseEnd_775706 := by
    simpa [prefixWord, tailWord_775706, baseEnd_775706] using wordTrace_append hprefix tailTrace_775706
  have hstable : (prefixWord ++ tailWord_775706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775706).length < 2 ^ (prefixWord ++ tailWord_775706).sum := by decide
  have hdescent : baseEnd_775706 < baseStart_775706 := by decide
  rcases family_descends (prefixWord ++ tailWord_775706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775756 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_775756 : Nat := 118140960795 + 775756 * 2 ^ 59
def prefixEnd_775756 : Nat := 4983230072969 + 3 ^ 40 * 775756 * 2
def baseEnd_775756 : Nat := 398335698609372084782369

theorem tailTrace_775756 : CollatzResearch.WordTrace tailWord_775756 prefixEnd_775756 398335698609372084782369 := by
  unfold tailWord_775756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14147072888787987710977561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18862763851717316947970081 14147072888787987710977561)
  ·
    refine ⟨10610304666590990783233171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14147072888787987710977561 10610304666590990783233171)
    ·
      refine ⟨15915456999886486174849757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10610304666590990783233171 15915456999886486174849757)
      ·
        refine ⟨5968296374957432315568659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15915456999886486174849757 5968296374957432315568659)
        ·
          refine ⟨8952444562436148473352989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968296374957432315568659 8952444562436148473352989)
          ·
            refine ⟨3357166710913555677507371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8952444562436148473352989 3357166710913555677507371)
            ·
              refine ⟨5035750066370333516261057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357166710913555677507371 5035750066370333516261057)
              ·
                refine ⟨3776812549777750137195793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035750066370333516261057 3776812549777750137195793)
                ·
                  refine ⟨2832609412333312602896845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776812549777750137195793 2832609412333312602896845)
                  ·
                    refine ⟨1062228529624992226086317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2832609412333312602896845 1062228529624992226086317)
                    ·
                      refine ⟨398335698609372084782369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062228529624992226086317 398335698609372084782369)
                      ·
                        rfl

theorem cell23_775756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_775756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775756 prefixEnd_775756 := by exact prefixLift 775756
  have htrace : WordTrace (prefixWord ++ tailWord_775756) baseStart_775756 baseEnd_775756 := by
    simpa [prefixWord, tailWord_775756, baseEnd_775756] using wordTrace_append hprefix tailTrace_775756
  have hstable : (prefixWord ++ tailWord_775756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775756).length < 2 ^ (prefixWord ++ tailWord_775756).sum := by decide
  have hdescent : baseEnd_775756 < baseStart_775756 := by decide
  rcases family_descends (prefixWord ++ tailWord_775756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775757 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_775757 : Nat := 118140960795 + 775757 * 2 ^ 59
def prefixEnd_775757 : Nat := 4983230072969 + 3 ^ 40 * 775757 * 2
def baseEnd_775757 : Nat := 398336212090026580869865

theorem tailTrace_775757 : CollatzResearch.WordTrace tailWord_775757 prefixEnd_775757 398336212090026580869865 := by
  unfold tailWord_775757
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294182250572352592741525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18862788167048235061827683 28294182250572352592741525)
  ·
    refine ⟨1326289792995579027784759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28294182250572352592741525 1326289792995579027784759)
    ·
      refine ⟨1989434689493368541677139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326289792995579027784759 1989434689493368541677139)
      ·
        refine ⟨2984152034240052812515709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989434689493368541677139 2984152034240052812515709)
        ·
          refine ⟨1119057012840019804693391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984152034240052812515709 1119057012840019804693391)
          ·
            refine ⟨1678585519260029707040087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119057012840019804693391 1678585519260029707040087)
            ·
              refine ⟨2517878278890044560560131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678585519260029707040087 2517878278890044560560131)
              ·
                refine ⟨3776817418335066840840197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517878278890044560560131 3776817418335066840840197)
                ·
                  refine ⟨708153265937825032657537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3776817418335066840840197 708153265937825032657537)
                  ·
                    refine ⟨531114949453368774493153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 708153265937825032657537 531114949453368774493153)
                    ·
                      refine ⟨398336212090026580869865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531114949453368774493153 398336212090026580869865)
                      ·
                        rfl

theorem cell23_775757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_775757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775757 prefixEnd_775757 := by exact prefixLift 775757
  have htrace : WordTrace (prefixWord ++ tailWord_775757) baseStart_775757 baseEnd_775757 := by
    simpa [prefixWord, tailWord_775757, baseEnd_775757] using wordTrace_append hprefix tailTrace_775757
  have hstable : (prefixWord ++ tailWord_775757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775757).length < 2 ^ (prefixWord ++ tailWord_775757).sum := by decide
  have hdescent : baseEnd_775757 < baseStart_775757 := by decide
  rcases family_descends (prefixWord ++ tailWord_775757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775759 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 4, 5]
def baseStart_775759 : Nat := 118140960795 + 775759 * 2 ^ 59
def prefixEnd_775759 : Nat := 4983230072969 + 3 ^ 40 * 775759 * 2
def baseEnd_775759 : Nat := 132779079683778524348285

theorem tailTrace_775759 : CollatzResearch.WordTrace tailWord_775759 prefixEnd_775759 132779079683778524348285 := by
  unfold tailWord_775759
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294255196565106934314331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18862836797710071289542887 28294255196565106934314331)
  ·
    refine ⟨42441382794847660401471497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28294255196565106934314331 42441382794847660401471497)
    ·
      refine ⟨31831037096135745301103623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42441382794847660401471497 31831037096135745301103623)
      ·
        refine ⟨47746555644203617951655435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31831037096135745301103623 47746555644203617951655435)
        ·
          refine ⟨71619833466305426927483153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47746555644203617951655435 71619833466305426927483153)
          ·
            refine ⟨53714875099729070195612365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71619833466305426927483153 53714875099729070195612365)
            ·
              refine ⟨20143078162398401323354637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53714875099729070195612365 20143078162398401323354637)
              ·
                refine ⟨7553654310899400496257989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20143078162398401323354637 7553654310899400496257989)
                ·
                  refine ⟨1416310183293637593048373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7553654310899400496257989 1416310183293637593048373)
                  ·
                    refine ⟨132779079683778524348285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1416310183293637593048373 132779079683778524348285)
                    ·
                      rfl

theorem cell23_775759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_775759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775759 prefixEnd_775759 := by exact prefixLift 775759
  have htrace : WordTrace (prefixWord ++ tailWord_775759) baseStart_775759 baseEnd_775759 := by
    simpa [prefixWord, tailWord_775759, baseEnd_775759] using wordTrace_append hprefix tailTrace_775759
  have hstable : (prefixWord ++ tailWord_775759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775759).length < 2 ^ (prefixWord ++ tailWord_775759).sum := by decide
  have hdescent : baseEnd_775759 < baseStart_775759 := by decide
  rcases family_descends (prefixWord ++ tailWord_775759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775769 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 5]
def baseStart_775769 : Nat := 118140960795 + 775769 * 2 ^ 59
def prefixEnd_775769 : Nat := 4983230072969 + 3 ^ 40 * 775769 * 2
def baseEnd_775769 : Nat := 398342373857880533919809

theorem tailTrace_775769 : CollatzResearch.WordTrace tailWord_775769 prefixEnd_775769 398342373857880533919809 := by
  unfold tailWord_775769
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294619926528878642178361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18863079951019252428118907 28294619926528878642178361)
  ·
    refine ⟨21220964944896658981633771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28294619926528878642178361 21220964944896658981633771)
    ·
      refine ⟨31831447417344988472450657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21220964944896658981633771 31831447417344988472450657)
      ·
        refine ⟨23873585563008741354337993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31831447417344988472450657 23873585563008741354337993)
        ·
          refine ⟨17905189172256556015753495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23873585563008741354337993 17905189172256556015753495)
          ·
            refine ⟨26857783758384834023630243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17905189172256556015753495 26857783758384834023630243)
            ·
              refine ⟨40286675637577251035445365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26857783758384834023630243 40286675637577251035445365)
              ·
                refine ⟨3776875841022867284573003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40286675637577251035445365 3776875841022867284573003)
                ·
                  refine ⟨5665313761534300926859505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776875841022867284573003 5665313761534300926859505)
                  ·
                    refine ⟨4248985321150725695144629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5665313761534300926859505 4248985321150725695144629)
                    ·
                      refine ⟨398342373857880533919809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4248985321150725695144629 398342373857880533919809)
                      ·
                        rfl

theorem cell23_775769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_775769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775769 prefixEnd_775769 := by exact prefixLift 775769
  have htrace : WordTrace (prefixWord ++ tailWord_775769) baseStart_775769 baseEnd_775769 := by
    simpa [prefixWord, tailWord_775769, baseEnd_775769] using wordTrace_append hprefix tailTrace_775769
  have hstable : (prefixWord ++ tailWord_775769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775769).length < 2 ^ (prefixWord ++ tailWord_775769).sum := by decide
  have hdescent : baseEnd_775769 < baseStart_775769 := by decide
  rcases family_descends (prefixWord ++ tailWord_775769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775799 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_775799 : Nat := 118140960795 + 775799 * 2 ^ 59
def prefixEnd_775799 : Nat := 4983230072969 + 3 ^ 40 * 775799 * 2
def baseEnd_775799 : Nat := 398357778277515416544671

theorem tailTrace_775799 : CollatzResearch.WordTrace tailWord_775799 prefixEnd_775799 398357778277515416544671 := by
  unfold tailWord_775799
  simp only [CollatzResearch.WordTrace]
  refine ⟨28295714116420193765770451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18863809410946795843846967 28295714116420193765770451)
  ·
    refine ⟨42443571174630290648655677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28295714116420193765770451 42443571174630290648655677)
    ·
      refine ⟨15916339190486358993245879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42443571174630290648655677 15916339190486358993245879)
      ·
        refine ⟨23874508785729538489868819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15916339190486358993245879 23874508785729538489868819)
        ·
          refine ⟨35811763178594307734803229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23874508785729538489868819 35811763178594307734803229)
          ·
            refine ⟨13429411191972865400551211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35811763178594307734803229 13429411191972865400551211)
            ·
              refine ⟨20144116787959298100826817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13429411191972865400551211 20144116787959298100826817)
              ·
                refine ⟨15108087590969473575620113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20144116787959298100826817 15108087590969473575620113)
                ·
                  refine ⟨11331065693227105181715085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15108087590969473575620113 11331065693227105181715085)
                  ·
                    refine ⟨4249149634960164443143157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11331065693227105181715085 4249149634960164443143157)
                    ·
                      refine ⟨398357778277515416544671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4249149634960164443143157 398357778277515416544671)
                      ·
                        rfl

theorem cell23_775799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_775799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775799 prefixEnd_775799 := by exact prefixLift 775799
  have htrace : WordTrace (prefixWord ++ tailWord_775799) baseStart_775799 baseEnd_775799 := by
    simpa [prefixWord, tailWord_775799, baseEnd_775799] using wordTrace_append hprefix tailTrace_775799
  have hstable : (prefixWord ++ tailWord_775799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775799).length < 2 ^ (prefixWord ++ tailWord_775799).sum := by decide
  have hdescent : baseEnd_775799 < baseStart_775799 := by decide
  rcases family_descends (prefixWord ++ tailWord_775799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775819 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 8]
def baseStart_775819 : Nat := 118140960795 + 775819 * 2 ^ 59
def prefixEnd_775819 : Nat := 4983230072969 + 3 ^ 40 * 775819 * 2
def baseEnd_775819 : Nat := 44263116432289482032731

theorem tailTrace_775819 : CollatzResearch.WordTrace tailWord_775819 prefixEnd_775819 44263116432289482032731 := by
  unfold tailWord_775819
  simp only [CollatzResearch.WordTrace]
  refine ⟨28296443576347737181498511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18864295717565158120999007 28296443576347737181498511)
  ·
    refine ⟨42444665364521605772247767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28296443576347737181498511 42444665364521605772247767)
    ·
      refine ⟨63666998046782408658371651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42444665364521605772247767 63666998046782408658371651)
      ·
        refine ⟨95500497070173612987557477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63666998046782408658371651 95500497070173612987557477)
        ·
          refine ⟨17906343200657552435167027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95500497070173612987557477 17906343200657552435167027)
          ·
            refine ⟨26859514800986328652750541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17906343200657552435167027 26859514800986328652750541)
            ·
              refine ⟨10072318050369873244781453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26859514800986328652750541 10072318050369873244781453)
              ·
                refine ⟨3777119268888702466793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10072318050369873244781453 3777119268888702466793045)
                ·
                  refine ⟨44263116432289482032731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3777119268888702466793045 44263116432289482032731)
                  ·
                    rfl

theorem cell23_775819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_775819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775819 prefixEnd_775819 := by exact prefixLift 775819
  have htrace : WordTrace (prefixWord ++ tailWord_775819) baseStart_775819 baseEnd_775819 := by
    simpa [prefixWord, tailWord_775819, baseEnd_775819] using wordTrace_append hprefix tailTrace_775819
  have hstable : (prefixWord ++ tailWord_775819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775819).length < 2 ^ (prefixWord ++ tailWord_775819).sum := by decide
  have hdescent : baseEnd_775819 < baseStart_775819 := by decide
  rcases family_descends (prefixWord ++ tailWord_775819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775903 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_775903 : Nat := 118140960795 + 775903 * 2 ^ 59
def prefixEnd_775903 : Nat := 4983230072969 + 3 ^ 40 * 775903 * 2
def baseEnd_775903 : Nat := 398411180265583009644193

theorem tailTrace_775903 : CollatzResearch.WordTrace tailWord_775903 prefixEnd_775903 398411180265583009644193 := by
  unfold tailWord_775903
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299507308043419527556363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18866338205362279685037575 28299507308043419527556363)
  ·
    refine ⟨42449260962065129291334545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28299507308043419527556363 42449260962065129291334545)
    ·
      refine ⟨31836945721548846968500909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42449260962065129291334545 31836945721548846968500909)
      ·
        refine ⟨11938854645580817613187841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31836945721548846968500909 11938854645580817613187841)
        ·
          refine ⟨8954140984185613209890881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11938854645580817613187841 8954140984185613209890881)
          ·
            refine ⟨6715605738139209907418161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8954140984185613209890881 6715605738139209907418161)
            ·
              refine ⟨5036704303604407430563621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715605738139209907418161 5036704303604407430563621)
              ·
                refine ⟨944382056925826393230679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5036704303604407430563621 944382056925826393230679)
                ·
                  refine ⟨1416573085388739589846019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944382056925826393230679 1416573085388739589846019)
                  ·
                    refine ⟨2124859628083109384769029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1416573085388739589846019 2124859628083109384769029)
                    ·
                      refine ⟨398411180265583009644193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2124859628083109384769029 398411180265583009644193)
                      ·
                        rfl

theorem cell23_775903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_775903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775903 prefixEnd_775903 := by exact prefixLift 775903
  have htrace : WordTrace (prefixWord ++ tailWord_775903) baseStart_775903 baseEnd_775903 := by
    simpa [prefixWord, tailWord_775903, baseEnd_775903] using wordTrace_append hprefix tailTrace_775903
  have hstable : (prefixWord ++ tailWord_775903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775903).length < 2 ^ (prefixWord ++ tailWord_775903).sum := by decide
  have hdescent : baseEnd_775903 < baseStart_775903 := by decide
  rcases family_descends (prefixWord ++ tailWord_775903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775917 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_775917 : Nat := 118140960795 + 775917 * 2 ^ 59
def prefixEnd_775917 : Nat := 4983230072969 + 3 ^ 40 * 775917 * 2
def baseEnd_775917 : Nat := 132806122998248651623043

theorem tailTrace_775917 : CollatzResearch.WordTrace tailWord_775917 prefixEnd_775917 132806122998248651623043 := by
  unfold tailWord_775917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28300017929992699918566005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18866678619995133279044003 28300017929992699918566005)
  ·
    refine ⟨2653126680936815617365563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28300017929992699918566005 2653126680936815617365563)
    ·
      refine ⟨3979690021405223426048345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653126680936815617365563 3979690021405223426048345)
      ·
        refine ⟨2984767516053917569536259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979690021405223426048345 2984767516053917569536259)
        ·
          refine ⟨4477151274080876354304389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984767516053917569536259 4477151274080876354304389)
          ·
            refine ⟨839465863890164316432073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4477151274080876354304389 839465863890164316432073)
            ·
              refine ⟨629599397917623237324055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839465863890164316432073 629599397917623237324055)
              ·
                refine ⟨944399096876434855986083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629599397917623237324055 944399096876434855986083)
                ·
                  refine ⟨1416598645314652283979125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944399096876434855986083 1416598645314652283979125)
                  ·
                    refine ⟨132806122998248651623043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1416598645314652283979125 132806122998248651623043)
                    ·
                      rfl

theorem cell23_775917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_775917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775917 prefixEnd_775917 := by exact prefixLift 775917
  have htrace : WordTrace (prefixWord ++ tailWord_775917) baseStart_775917 baseEnd_775917 := by
    simpa [prefixWord, tailWord_775917, baseEnd_775917] using wordTrace_append hprefix tailTrace_775917
  have hstable : (prefixWord ++ tailWord_775917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775917).length < 2 ^ (prefixWord ++ tailWord_775917).sum := by decide
  have hdescent : baseEnd_775917 < baseStart_775917 := by decide
  rcases family_descends (prefixWord ++ tailWord_775917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775954 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_775954 : Nat := 118140960795 + 775954 * 2 ^ 59
def prefixEnd_775954 : Nat := 4983230072969 + 3 ^ 40 * 775954 * 2
def baseEnd_775954 : Nat := 398437367778962310106459

theorem tailTrace_775954 : CollatzResearch.WordTrace tailWord_775954 prefixEnd_775954 398437367778962310106459 := by
  unfold tailWord_775954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075341857714663809415729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18867578287239103491775277 7075341857714663809415729)
  ·
    refine ⟨5306506393285997857061797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7075341857714663809415729 5306506393285997857061797)
    ·
      refine ⟨994969948741124598199087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5306506393285997857061797 994969948741124598199087)
      ·
        refine ⟨1492454923111686897298631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994969948741124598199087 1492454923111686897298631)
        ·
          refine ⟨2238682384667530345947947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492454923111686897298631 2238682384667530345947947)
          ·
            refine ⟨3358023577001295518921921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238682384667530345947947 3358023577001295518921921)
            ·
              refine ⟨2518517682750971639191441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358023577001295518921921 2518517682750971639191441)
              ·
                refine ⟨1888888262063228729393581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518517682750971639191441 1888888262063228729393581)
                ·
                  refine ⟨708333098273710773522593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1888888262063228729393581 708333098273710773522593)
                  ·
                    refine ⟨531249823705283080141945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 708333098273710773522593 531249823705283080141945)
                    ·
                      refine ⟨398437367778962310106459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531249823705283080141945 398437367778962310106459)
                      ·
                        rfl

theorem cell23_775954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_775954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775954 prefixEnd_775954 := by exact prefixLift 775954
  have htrace : WordTrace (prefixWord ++ tailWord_775954) baseStart_775954 baseEnd_775954 := by
    simpa [prefixWord, tailWord_775954, baseEnd_775954] using wordTrace_append hprefix tailTrace_775954
  have hstable : (prefixWord ++ tailWord_775954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775954).length < 2 ^ (prefixWord ++ tailWord_775954).sum := by decide
  have hdescent : baseEnd_775954 < baseStart_775954 := by decide
  rcases family_descends (prefixWord ++ tailWord_775954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775970 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_775970 : Nat := 118140960795 + 775970 * 2 ^ 59
def prefixEnd_775970 : Nat := 4983230072969 + 3 ^ 40 * 775970 * 2
def baseEnd_775970 : Nat := 398445583469434247506385

theorem tailTrace_775970 : CollatzResearch.WordTrace tailWord_775970 prefixEnd_775970 398445583469434247506385 := by
  unfold tailWord_775970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075487749700172492561341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18867967332533793313496909 7075487749700172492561341)
  ·
    refine ⟨2653307906137564684710503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7075487749700172492561341 2653307906137564684710503)
    ·
      refine ⟨3979961859206347027065755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653307906137564684710503 3979961859206347027065755)
      ·
        refine ⟨5969942788809520540598633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3979961859206347027065755 5969942788809520540598633)
        ·
          refine ⟨4477457091607140405448975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5969942788809520540598633 4477457091607140405448975)
          ·
            refine ⟨6716185637410710608173463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477457091607140405448975 6716185637410710608173463)
            ·
              refine ⟨10074278456116065912260195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716185637410710608173463 10074278456116065912260195)
              ·
                refine ⟨15111417684174098868390293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074278456116065912260195 15111417684174098868390293)
                ·
                  refine ⟨708347703945660884455795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15111417684174098868390293 708347703945660884455795)
                  ·
                    refine ⟨1062521555918491326683693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708347703945660884455795 1062521555918491326683693)
                    ·
                      refine ⟨398445583469434247506385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062521555918491326683693 398445583469434247506385)
                      ·
                        rfl

theorem cell23_775970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_775970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775970 prefixEnd_775970 := by exact prefixLift 775970
  have htrace : WordTrace (prefixWord ++ tailWord_775970) baseStart_775970 baseEnd_775970 := by
    simpa [prefixWord, tailWord_775970, baseEnd_775970] using wordTrace_append hprefix tailTrace_775970
  have hstable : (prefixWord ++ tailWord_775970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775970).length < 2 ^ (prefixWord ++ tailWord_775970).sum := by decide
  have hdescent : baseEnd_775970 < baseStart_775970 := by decide
  rcases family_descends (prefixWord ++ tailWord_775970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_775988 : List Nat := [2, 5, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_775988 : Nat := 118140960795 + 775988 * 2 ^ 59
def prefixEnd_775988 : Nat := 4983230072969 + 3 ^ 40 * 775988 * 2
def baseEnd_775988 : Nat := 398454826121215177081303

theorem tailTrace_775988 : CollatzResearch.WordTrace tailWord_775988 prefixEnd_775988 398454826121215177081303 := by
  unfold tailWord_775988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151303756367739522200309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18868405008490319362933745 14151303756367739522200309)
  ·
    refine ⟨1326684727159475580206279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14151303756367739522200309 1326684727159475580206279)
    ·
      refine ⟨1990027090739213370309419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1326684727159475580206279 1990027090739213370309419)
      ·
        refine ⟨2985040636108820055464129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990027090739213370309419 2985040636108820055464129)
        ·
          refine ⟨2238780477081615041598097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985040636108820055464129 2238780477081615041598097)
          ·
            refine ⟨1679085357811211281198573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2238780477081615041598097 1679085357811211281198573)
            ·
              refine ⟨629657009179204230449465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679085357811211281198573 629657009179204230449465)
              ·
                refine ⟨472242756884403172837099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629657009179204230449465 472242756884403172837099)
                ·
                  refine ⟨708364135326604759255649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472242756884403172837099 708364135326604759255649)
                  ·
                    refine ⟨531273101494953569441737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 708364135326604759255649 531273101494953569441737)
                    ·
                      refine ⟨398454826121215177081303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531273101494953569441737 398454826121215177081303)
                      ·
                        rfl

theorem cell23_775988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_775988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_775988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_775988 prefixEnd_775988 := by exact prefixLift 775988
  have htrace : WordTrace (prefixWord ++ tailWord_775988) baseStart_775988 baseEnd_775988 := by
    simpa [prefixWord, tailWord_775988, baseEnd_775988] using wordTrace_append hprefix tailTrace_775988
  have hstable : (prefixWord ++ tailWord_775988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_775988).length < 2 ^ (prefixWord ++ tailWord_775988).sum := by decide
  have hdescent : baseEnd_775988 < baseStart_775988 := by decide
  rcases family_descends (prefixWord ++ tailWord_775988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776010 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2]
def baseStart_776010 : Nat := 118140960795 + 776010 * 2 ^ 59
def prefixEnd_776010 : Nat := 4983230072969 + 3 ^ 40 * 776010 * 2
def baseEnd_776010 : Nat := 398466122695614091006201

theorem tailTrace_776010 : CollatzResearch.WordTrace tailWord_776010 prefixEnd_776010 398466122695614091006201 := by
  unfold tailWord_776010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075852479663944200425371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18868939945770517867800989 7075852479663944200425371)
  ·
    refine ⟨10613778719495916300638057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075852479663944200425371 10613778719495916300638057)
    ·
      refine ⟨7960334039621937225478543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10613778719495916300638057 7960334039621937225478543)
      ·
        refine ⟨11940501059432905838217815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7960334039621937225478543 11940501059432905838217815)
        ·
          refine ⟨17910751589149358757326723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940501059432905838217815 17910751589149358757326723)
          ·
            refine ⟨26866127383724038135990085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17910751589149358757326723 26866127383724038135990085)
            ·
              refine ⟨5037398884448257150498141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26866127383724038135990085 5037398884448257150498141)
              ·
                refine ⟨1889024581668096431436803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5037398884448257150498141 1889024581668096431436803)
                ·
                  refine ⟨2833536872502144647155205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889024581668096431436803 2833536872502144647155205)
                  ·
                    refine ⟨531288163594152121341601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833536872502144647155205 531288163594152121341601)
                    ·
                      refine ⟨398466122695614091006201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531288163594152121341601 398466122695614091006201)
                      ·
                        rfl

theorem cell23_776010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_776010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776010 prefixEnd_776010 := by exact prefixLift 776010
  have htrace : WordTrace (prefixWord ++ tailWord_776010) baseStart_776010 baseEnd_776010 := by
    simpa [prefixWord, tailWord_776010, baseEnd_776010] using wordTrace_append hprefix tailTrace_776010
  have hstable : (prefixWord ++ tailWord_776010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776010).length < 2 ^ (prefixWord ++ tailWord_776010).sum := by decide
  have hdescent : baseEnd_776010 < baseStart_776010 := by decide
  rcases family_descends (prefixWord ++ tailWord_776010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776016 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 9]
def baseStart_776016 : Nat := 118140960795 + 776016 * 2 ^ 59
def prefixEnd_776016 : Nat := 4983230072969 + 3 ^ 40 * 776016 * 2
def baseEnd_776016 : Nat := 44274355953282340836797

theorem tailTrace_776016 : CollatzResearch.WordTrace tailWord_776016 prefixEnd_776016 44274355953282340836797 := by
  unfold tailWord_776016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151814378317019913209951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18869085837756026550946601 14151814378317019913209951)
  ·
    refine ⟨21227721567475529869814927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151814378317019913209951 21227721567475529869814927)
    ·
      refine ⟨31841582351213294804722391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21227721567475529869814927 31841582351213294804722391)
      ·
        refine ⟨47762373526819942207083587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31841582351213294804722391 47762373526819942207083587)
        ·
          refine ⟨71643560290229913310625381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47762373526819942207083587 71643560290229913310625381)
          ·
            refine ⟨13433167554418108745742259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71643560290229913310625381 13433167554418108745742259)
            ·
              refine ⟨20149751331627163118613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13433167554418108745742259 20149751331627163118613389)
              ·
                refine ⟨7556156749360186169480021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20149751331627163118613389 7556156749360186169480021)
                ·
                  refine ⟨44274355953282340836797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7556156749360186169480021 44274355953282340836797)
                  ·
                    rfl

theorem cell23_776016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_776016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776016 prefixEnd_776016 := by exact prefixLift 776016
  have htrace : WordTrace (prefixWord ++ tailWord_776016) baseStart_776016 baseEnd_776016 := by
    simpa [prefixWord, tailWord_776016, baseEnd_776016] using wordTrace_append hprefix tailTrace_776016
  have hstable : (prefixWord ++ tailWord_776016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776016).length < 2 ^ (prefixWord ++ tailWord_776016).sum := by decide
  have hdescent : baseEnd_776016 < baseStart_776016 := by decide
  rcases family_descends (prefixWord ++ tailWord_776016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
