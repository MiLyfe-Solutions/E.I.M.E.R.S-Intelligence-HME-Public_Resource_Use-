import V185TrunkScan21Chunk128

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1571639 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 4]
def baseStart_1571639 : Nat := 118140960795 + 1571639 * 2 ^ 59
def prefixEnd_1571639 : Nat := 4983230072969 + 3 ^ 40 * 1571639 * 2
def baseEnd_1571639 : Nat := 358669432156302972837631

theorem tailTrace_1571639 : CollatzResearch.WordTrace tailWord_1571639 prefixEnd_1571639 358669432156302972837631 := by
  unfold tailWord_1571639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57322383553227792416733971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38214922368818528277822647 57322383553227792416733971)
  ·
    refine ⟨85983575329841688625100957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57322383553227792416733971 85983575329841688625100957)
    ·
      refine ⟨32243840748690633234412859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85983575329841688625100957 32243840748690633234412859)
      ·
        refine ⟨48365761123035949851619289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32243840748690633234412859 48365761123035949851619289)
        ·
          refine ⟨36274320842276962388714467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48365761123035949851619289 36274320842276962388714467)
          ·
            refine ⟨54411481263415443583071701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36274320842276962388714467 54411481263415443583071701)
            ·
              refine ⟨1275269092111299458978243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54411481263415443583071701 1275269092111299458978243)
              ·
                refine ⟨1912903638166949188467365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275269092111299458978243 1912903638166949188467365)
                ·
                  refine ⟨358669432156302972837631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1912903638166949188467365 358669432156302972837631)
                  ·
                    rfl

theorem cell21_1571639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_1571639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571639 prefixEnd_1571639 := by exact prefixLift 1571639
  have htrace : WordTrace (prefixWord ++ tailWord_1571639) baseStart_1571639 baseEnd_1571639 := by
    simpa [prefixWord, tailWord_1571639, baseEnd_1571639] using wordTrace_append hprefix tailTrace_1571639
  have hstable : (prefixWord ++ tailWord_1571639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571639).length < 2 ^ (prefixWord ++ tailWord_1571639).sum := by decide
  have hdescent : baseEnd_1571639 < baseStart_1571639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571684 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1571684 : Nat := 118140960795 + 1571684 * 2 ^ 59
def prefixEnd_1571684 : Nat := 4983230072969 + 3 ^ 40 * 1571684 * 2
def baseEnd_1571684 : Nat := 358679701769392894587539

theorem tailTrace_1571684 : CollatzResearch.WordTrace tailWord_1571684 prefixEnd_1571684 358679701769392894587539 := by
  unfold tailWord_1571684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662012419032382551061053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38216016558709843401414737 28662012419032382551061053)
  ·
    refine ⟨10748254657137143456647895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28662012419032382551061053 10748254657137143456647895)
    ·
      refine ⟨16122381985705715184971843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10748254657137143456647895 16122381985705715184971843)
      ·
        refine ⟨24183572978558572777457765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16122381985705715184971843 24183572978558572777457765)
        ·
          refine ⟨4534419933479732395773331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24183572978558572777457765 4534419933479732395773331)
          ·
            refine ⟨6801629900219598593659997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534419933479732395773331 6801629900219598593659997)
            ·
              refine ⟨2550611212582349472622499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6801629900219598593659997 2550611212582349472622499)
              ·
                refine ⟨3825916818873524208933749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550611212582349472622499 3825916818873524208933749)
                ·
                  refine ⟨358679701769392894587539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3825916818873524208933749 358679701769392894587539)
                  ·
                    rfl

theorem cell21_1571684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1571684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571684 prefixEnd_1571684 := by exact prefixLift 1571684
  have htrace : WordTrace (prefixWord ++ tailWord_1571684) baseStart_1571684 baseEnd_1571684 := by
    simpa [prefixWord, tailWord_1571684, baseEnd_1571684] using wordTrace_append hprefix tailTrace_1571684
  have hstable : (prefixWord ++ tailWord_1571684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571684).length < 2 ^ (prefixWord ++ tailWord_1571684).sum := by decide
  have hdescent : baseEnd_1571684 < baseStart_1571684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571746 : List Nat := [3, 3, 1, 2, 2, 3, 1, 6]
def baseStart_1571746 : Nat := 118140960795 + 1571746 * 2 ^ 59
def prefixEnd_1571746 : Nat := 4983230072969 + 3 ^ 40 * 1571746 * 2
def baseEnd_1571746 : Nat := 119564617004698188184693

theorem tailTrace_1571746 : CollatzResearch.WordTrace tailWord_1571746 prefixEnd_1571746 119564617004698188184693 := by
  unfold tailWord_1571746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331571540960037422719773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38217524109226766460586061 14331571540960037422719773)
  ·
    refine ⟨5374339327860014033519915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14331571540960037422719773 5374339327860014033519915)
    ·
      refine ⟨8061508991790021050279873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374339327860014033519915 8061508991790021050279873)
      ·
        refine ⟨6046131743842515787709905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8061508991790021050279873 6046131743842515787709905)
        ·
          refine ⟨4534598807881886840782429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6046131743842515787709905 4534598807881886840782429)
          ·
            refine ⟨1700474552955707565293411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4534598807881886840782429 1700474552955707565293411)
            ·
              refine ⟨2550711829433561347940117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700474552955707565293411 2550711829433561347940117)
              ·
                refine ⟨119564617004698188184693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2550711829433561347940117 119564617004698188184693)
                ·
                  rfl

theorem cell21_1571746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_1571746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571746 prefixEnd_1571746 := by exact prefixLift 1571746
  have htrace : WordTrace (prefixWord ++ tailWord_1571746) baseStart_1571746 baseEnd_1571746 := by
    simpa [prefixWord, tailWord_1571746, baseEnd_1571746] using wordTrace_append hprefix tailTrace_1571746
  have hstable : (prefixWord ++ tailWord_1571746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571746).length < 2 ^ (prefixWord ++ tailWord_1571746).sum := by decide
  have hdescent : baseEnd_1571746 < baseStart_1571746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571774 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_1571774 : Nat := 118140960795 + 1571774 * 2 ^ 59
def prefixEnd_1571774 : Nat := 4983230072969 + 3 ^ 40 * 1571774 * 2
def baseEnd_1571774 : Nat := 358700240995572738087355

theorem tailTrace_1571774 : CollatzResearch.WordTrace tailWord_1571774 prefixEnd_1571774 358700240995572738087355 := by
  unfold tailWord_1571774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165913425967338809112297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38218204938492473648598917 7165913425967338809112297)
  ·
    refine ⟨5374435069475504106834223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7165913425967338809112297 5374435069475504106834223)
    ·
      refine ⟨8061652604213256160251335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374435069475504106834223 8061652604213256160251335)
      ·
        refine ⟨12092478906319884240377003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8061652604213256160251335 12092478906319884240377003)
        ·
          refine ⟨18138718359479826360565505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12092478906319884240377003 18138718359479826360565505)
          ·
            refine ⟨13604038769609869770424129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18138718359479826360565505 13604038769609869770424129)
            ·
              refine ⟨10203029077207402327818097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13604038769609869770424129 10203029077207402327818097)
              ·
                refine ⟨7652271807905551745863573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10203029077207402327818097 7652271807905551745863573)
                ·
                  refine ⟨358700240995572738087355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7652271807905551745863573 358700240995572738087355)
                  ·
                    rfl

theorem cell21_1571774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_1571774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571774 prefixEnd_1571774 := by exact prefixLift 1571774
  have htrace : WordTrace (prefixWord ++ tailWord_1571774) baseStart_1571774 baseEnd_1571774 := by
    simpa [prefixWord, tailWord_1571774, baseEnd_1571774] using wordTrace_append hprefix tailTrace_1571774
  have hstable : (prefixWord ++ tailWord_1571774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571774).length < 2 ^ (prefixWord ++ tailWord_1571774).sum := by decide
  have hdescent : baseEnd_1571774 < baseStart_1571774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571788 : List Nat := [2, 2, 1, 4, 1, 1, 10]
def baseStart_1571788 : Nat := 118140960795 + 1571788 * 2 ^ 59
def prefixEnd_1571788 : Nat := 4983230072969 + 3 ^ 40 * 1571788 * 2
def baseEnd_1571788 : Nat := 39855937331812424983777

theorem tailTrace_1571788 : CollatzResearch.WordTrace tailWord_1571788 prefixEnd_1571788 39855937331812424983777 := by
  unfold tailWord_1571788
  simp only [CollatzResearch.WordTrace]
  refine ⟨28663909014843995431954009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38218545353125327242605345 28663909014843995431954009)
  ·
    refine ⟨21497931761132996573965507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28663909014843995431954009 21497931761132996573965507)
    ·
      refine ⟨32246897641699494860948261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497931761132996573965507 32246897641699494860948261)
      ·
        refine ⟨6046293307818655286427799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32246897641699494860948261 6046293307818655286427799)
        ·
          refine ⟨9069439961727982929641699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6046293307818655286427799 9069439961727982929641699)
          ·
            refine ⟨13604159942591974394462549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9069439961727982929641699 13604159942591974394462549)
            ·
              refine ⟨39855937331812424983777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13604159942591974394462549 39855937331812424983777)
              ·
                rfl

theorem cell21_1571788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 10].length) (baseStart_1571788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571788 prefixEnd_1571788 := by exact prefixLift 1571788
  have htrace : WordTrace (prefixWord ++ tailWord_1571788) baseStart_1571788 baseEnd_1571788 := by
    simpa [prefixWord, tailWord_1571788, baseEnd_1571788] using wordTrace_append hprefix tailTrace_1571788
  have hstable : (prefixWord ++ tailWord_1571788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571788).length < 2 ^ (prefixWord ++ tailWord_1571788).sum := by decide
  have hdescent : baseEnd_1571788 < baseStart_1571788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571791 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_1571791 : Nat := 118140960795 + 1571791 * 2 ^ 59
def prefixEnd_1571791 : Nat := 4983230072969 + 3 ^ 40 * 1571791 * 2
def baseEnd_1571791 : Nat := 358704120627184486303987

theorem tailTrace_1571791 : CollatzResearch.WordTrace tailWord_1571791 prefixEnd_1571791 358704120627184486303987 := by
  unfold tailWord_1571791
  simp only [CollatzResearch.WordTrace]
  refine ⟨57327927448677122376267227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38218618299118081584178151 57327927448677122376267227)
  ·
    refine ⟨85991891173015683564400841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57327927448677122376267227 85991891173015683564400841)
    ·
      refine ⟨64493918379761762673300631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85991891173015683564400841 64493918379761762673300631)
      ·
        refine ⟨96740877569642644009950947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64493918379761762673300631 96740877569642644009950947)
        ·
          refine ⟨145111316354463966014926421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96740877569642644009950947 145111316354463966014926421)
          ·
            refine ⟨1700523238528874601737419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 145111316354463966014926421 1700523238528874601737419)
            ·
              refine ⟨2550784857793311902606129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700523238528874601737419 2550784857793311902606129)
              ·
                refine ⟨1913088643344983926954597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550784857793311902606129 1913088643344983926954597)
                ·
                  refine ⟨358704120627184486303987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913088643344983926954597 358704120627184486303987)
                  ·
                    rfl

theorem cell21_1571791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_1571791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571791 prefixEnd_1571791 := by exact prefixLift 1571791
  have htrace : WordTrace (prefixWord ++ tailWord_1571791) baseStart_1571791 baseEnd_1571791 := by
    simpa [prefixWord, tailWord_1571791, baseEnd_1571791] using wordTrace_append hprefix tailTrace_1571791
  have hstable : (prefixWord ++ tailWord_1571791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571791).length < 2 ^ (prefixWord ++ tailWord_1571791).sum := by decide
  have hdescent : baseEnd_1571791 < baseStart_1571791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571833 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_1571833 : Nat := 118140960795 + 1571833 * 2 ^ 59
def prefixEnd_1571833 : Nat := 4983230072969 + 3 ^ 40 * 1571833 * 2
def baseEnd_1571833 : Nat := 358713705599401746603901

theorem tailTrace_1571833 : CollatzResearch.WordTrace tailWord_1571833 prefixEnd_1571833 358713705599401746603901 := by
  unfold tailWord_1571833
  simp only [CollatzResearch.WordTrace]
  refine ⟨57329459314524963549296153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38219639543016642366197435 57329459314524963549296153)
  ·
    refine ⟨42997094485893722661972115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57329459314524963549296153 42997094485893722661972115)
    ·
      refine ⟨64495641728840583992958173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42997094485893722661972115 64495641728840583992958173)
      ·
        refine ⟨24185865648315218997359315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64495641728840583992958173 24185865648315218997359315)
        ·
          refine ⟨36278798472472828496038973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24185865648315218997359315 36278798472472828496038973)
          ·
            refine ⟨13604549427177310686014615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36278798472472828496038973 13604549427177310686014615)
            ·
              refine ⟨20406824140765966029021923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13604549427177310686014615 20406824140765966029021923)
              ·
                refine ⟨30610236211148949043532885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20406824140765966029021923 30610236211148949043532885)
                ·
                  refine ⟨358713705599401746603901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30610236211148949043532885 358713705599401746603901)
                  ·
                    rfl

theorem cell21_1571833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_1571833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571833 prefixEnd_1571833 := by exact prefixLift 1571833
  have htrace : WordTrace (prefixWord ++ tailWord_1571833) baseStart_1571833 baseEnd_1571833 := by
    simpa [prefixWord, tailWord_1571833, baseEnd_1571833] using wordTrace_append hprefix tailTrace_1571833
  have hstable : (prefixWord ++ tailWord_1571833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571833).length < 2 ^ (prefixWord ++ tailWord_1571833).sum := by decide
  have hdescent : baseEnd_1571833 < baseStart_1571833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571850 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1571850 : Nat := 118140960795 + 1571850 * 2 ^ 59
def prefixEnd_1571850 : Nat := 4983230072969 + 3 ^ 40 * 1571850 * 2
def baseEnd_1571850 : Nat := 358717585231013494820533

theorem tailTrace_1571850 : CollatzResearch.WordTrace tailWord_1571850 prefixEnd_1571850 358717585231013494820533 := by
  unfold tailWord_1571850
  simp only [CollatzResearch.WordTrace]
  refine ⟨14332519838865843863166251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38220052903642250301776669 14332519838865843863166251)
  ·
    refine ⟨21498779758298765794749377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14332519838865843863166251 21498779758298765794749377)
    ·
      refine ⟨16124084818724074346062033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21498779758298765794749377 16124084818724074346062033)
      ·
        refine ⟨12093063614043055759546525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16124084818724074346062033 12093063614043055759546525)
        ·
          refine ⟨4534898855266145909829947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12093063614043055759546525 4534898855266145909829947)
          ·
            refine ⟨6802348282899218864744921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534898855266145909829947 6802348282899218864744921)
            ·
              refine ⟨5101761212174414148558691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802348282899218864744921 5101761212174414148558691)
              ·
                refine ⟨7652641818261621222838037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101761212174414148558691 7652641818261621222838037)
                ·
                  refine ⟨358717585231013494820533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7652641818261621222838037 358717585231013494820533)
                  ·
                    rfl

theorem cell21_1571850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1571850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571850 prefixEnd_1571850 := by exact prefixLift 1571850
  have htrace : WordTrace (prefixWord ++ tailWord_1571850) baseStart_1571850 baseEnd_1571850 := by
    simpa [prefixWord, tailWord_1571850, baseEnd_1571850] using wordTrace_append hprefix tailTrace_1571850
  have hstable : (prefixWord ++ tailWord_1571850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571850).length < 2 ^ (prefixWord ++ tailWord_1571850).sum := by decide
  have hdescent : baseEnd_1571850 < baseStart_1571850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571864 : List Nat := [2, 1, 2, 3, 2, 2, 1, 8]
def baseStart_1571864 : Nat := 118140960795 + 1571864 * 2 ^ 59
def prefixEnd_1571864 : Nat := 4983230072969 + 3 ^ 40 * 1571864 * 2
def baseEnd_1571864 : Nat := 119573593407250860529057

theorem tailTrace_1571864 : CollatzResearch.WordTrace tailWord_1571864 prefixEnd_1571864 119573593407250860529057 := by
  unfold tailWord_1571864
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665294988706327921837323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38220393318275103895783097 28665294988706327921837323)
  ·
    refine ⟨42997942483059491882755985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665294988706327921837323 42997942483059491882755985)
    ·
      refine ⟨32248456862294618912066989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42997942483059491882755985 32248456862294618912066989)
      ·
        refine ⟨12093171323360482092025121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32248456862294618912066989 12093171323360482092025121)
        ·
          refine ⟨9069878492520361569018841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12093171323360482092025121 9069878492520361569018841)
          ·
            refine ⟨6802408869390271176764131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9069878492520361569018841 6802408869390271176764131)
            ·
              refine ⟨10203613304085406765146197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6802408869390271176764131 10203613304085406765146197)
              ·
                refine ⟨119573593407250860529057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10203613304085406765146197 119573593407250860529057)
                ·
                  rfl

theorem cell21_1571864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_1571864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571864 prefixEnd_1571864 := by exact prefixLift 1571864
  have htrace : WordTrace (prefixWord ++ tailWord_1571864) baseStart_1571864 baseEnd_1571864 := by
    simpa [prefixWord, tailWord_1571864, baseEnd_1571864] using wordTrace_append hprefix tailTrace_1571864
  have hstable : (prefixWord ++ tailWord_1571864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571864).length < 2 ^ (prefixWord ++ tailWord_1571864).sum := by decide
  have hdescent : baseEnd_1571864 < baseStart_1571864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571909 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_1571909 : Nat := 118140960795 + 1571909 * 2 ^ 59
def prefixEnd_1571909 : Nat := 4983230072969 + 3 ^ 40 * 1571909 * 2
def baseEnd_1571909 : Nat := 358731049834842503337079

theorem tailTrace_1571909 : CollatzResearch.WordTrace tailWord_1571909 prefixEnd_1571909 358731049834842503337079 := by
  unfold tailWord_1571909
  simp only [CollatzResearch.WordTrace]
  refine ⟨57332231262249628529062781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38221487508166419019375187 57332231262249628529062781)
  ·
    refine ⟨21499586723343610698398543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57332231262249628529062781 21499586723343610698398543)
    ·
      refine ⟨32249380085015416047597815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21499586723343610698398543 32249380085015416047597815)
      ·
        refine ⟨48374070127523124071396723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32249380085015416047597815 48374070127523124071396723)
        ·
          refine ⟨72561105191284686107095085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48374070127523124071396723 72561105191284686107095085)
          ·
            refine ⟨27210414446731757290160657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72561105191284686107095085 27210414446731757290160657)
            ·
              refine ⟨20407810835048817967620493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27210414446731757290160657 20407810835048817967620493)
              ·
                refine ⟨7652929063143306737857685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20407810835048817967620493 7652929063143306737857685)
                ·
                  refine ⟨358731049834842503337079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7652929063143306737857685 358731049834842503337079)
                  ·
                    rfl

theorem cell21_1571909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_1571909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571909 prefixEnd_1571909 := by exact prefixLift 1571909
  have htrace : WordTrace (prefixWord ++ tailWord_1571909) baseStart_1571909 baseEnd_1571909 := by
    simpa [prefixWord, tailWord_1571909, baseEnd_1571909] using wordTrace_append hprefix tailTrace_1571909
  have hstable : (prefixWord ++ tailWord_1571909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571909).length < 2 ^ (prefixWord ++ tailWord_1571909).sum := by decide
  have hdescent : baseEnd_1571909 < baseStart_1571909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571912 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_1571912 : Nat := 118140960795 + 1571912 * 2 ^ 59
def prefixEnd_1571912 : Nat := 4983230072969 + 3 ^ 40 * 1571912 * 2
def baseEnd_1571912 : Nat := 358731734475715164787073

theorem tailTrace_1571912 : CollatzResearch.WordTrace tailWord_1571912 prefixEnd_1571912 358731734475715164787073 := by
  unfold tailWord_1571912
  simp only [CollatzResearch.WordTrace]
  refine ⟨28666170340619380020710995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38221560454159173360947993 28666170340619380020710995)
  ·
    refine ⟨42999255510929070031066493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28666170340619380020710995 42999255510929070031066493)
    ·
      refine ⟨16124720816598401261649935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42999255510929070031066493 16124720816598401261649935)
      ·
        refine ⟨24187081224897601892474903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16124720816598401261649935 24187081224897601892474903)
        ·
          refine ⟨36280621837346402838712355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24187081224897601892474903 36280621837346402838712355)
          ·
            refine ⟨54420932756019604258068533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36280621837346402838712355 54420932756019604258068533)
            ·
              refine ⟨5101962445876837899193925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54420932756019604258068533 5101962445876837899193925)
              ·
                refine ⟨956617958601907106098861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5101962445876837899193925 956617958601907106098861)
                ·
                  refine ⟨358731734475715164787073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956617958601907106098861 358731734475715164787073)
                  ·
                    rfl

theorem cell21_1571912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_1571912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571912 prefixEnd_1571912 := by exact prefixLift 1571912
  have htrace : WordTrace (prefixWord ++ tailWord_1571912) baseStart_1571912 baseEnd_1571912 := by
    simpa [prefixWord, tailWord_1571912, baseEnd_1571912] using wordTrace_append hprefix tailTrace_1571912
  have hstable : (prefixWord ++ tailWord_1571912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571912).length < 2 ^ (prefixWord ++ tailWord_1571912).sum := by decide
  have hdescent : baseEnd_1571912 < baseStart_1571912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571971 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_1571971 : Nat := 118140960795 + 1571971 * 2 ^ 59
def prefixEnd_1571971 : Nat := 4983230072969 + 3 ^ 40 * 1571971 * 2
def baseEnd_1571971 : Nat := 358745199079544173303619

theorem tailTrace_1571971 : CollatzResearch.WordTrace tailWord_1571971 prefixEnd_1571971 358745199079544173303619 := by
  unfold tailWord_1571971
  simp only [CollatzResearch.WordTrace]
  refine ⟨57334492588025013117819767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38222995058683342078546511 57334492588025013117819767)
  ·
    refine ⟨86001738882037519676729651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57334492588025013117819767 86001738882037519676729651)
    ·
      refine ⟨129002608323056279515094477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86001738882037519676729651 129002608323056279515094477)
      ·
        refine ⟨48375978121146104818160429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129002608323056279515094477 48375978121146104818160429)
        ·
          refine ⟨18140991795429789306810161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48375978121146104818160429 18140991795429789306810161)
          ·
            refine ⟨13605743846572341980107621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18140991795429789306810161 13605743846572341980107621)
            ·
              refine ⟨2551076971232314121270179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13605743846572341980107621 2551076971232314121270179)
              ·
                refine ⟨3826615456848471181905269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551076971232314121270179 3826615456848471181905269)
                ·
                  refine ⟨358745199079544173303619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3826615456848471181905269 358745199079544173303619)
                  ·
                    rfl

theorem cell21_1571971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_1571971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1571971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1571971 prefixEnd_1571971 := by exact prefixLift 1571971
  have htrace : WordTrace (prefixWord ++ tailWord_1571971) baseStart_1571971 baseEnd_1571971 := by
    simpa [prefixWord, tailWord_1571971, baseEnd_1571971] using wordTrace_append hprefix tailTrace_1571971
  have hstable : (prefixWord ++ tailWord_1571971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571971).length < 2 ^ (prefixWord ++ tailWord_1571971).sum := by decide
  have hdescent : baseEnd_1571971 < baseStart_1571971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572005 : List Nat := [1, 3, 1, 2, 1, 6, 1, 3, 3]
def baseStart_1572005 : Nat := 118140960795 + 1572005 * 2 ^ 59
def prefixEnd_1572005 : Nat := 4983230072969 + 3 ^ 40 * 1572005 * 2
def baseEnd_1572005 : Nat := 358752958342767669736883

theorem tailTrace_1572005 : CollatzResearch.WordTrace tailWord_1572005 prefixEnd_1572005 358752958342767669736883 := by
  unfold tailWord_1572005
  simp only [CollatzResearch.WordTrace]
  refine ⟨57335732669901836924557469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38223821779934557949704979 57335732669901836924557469)
  ·
    refine ⟨21500899751213188846709051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57335732669901836924557469 21500899751213188846709051)
    ·
      refine ⟨32251349626819783270063577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21500899751213188846709051 32251349626819783270063577)
      ·
        refine ⟨24188512220114837452547683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32251349626819783270063577 24188512220114837452547683)
        ·
          refine ⟨36282768330172256178821525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188512220114837452547683 36282768330172256178821525)
          ·
            refine ⟨1700754765476824508382259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36282768330172256178821525 1700754765476824508382259)
            ·
              refine ⟨2551132148215236762573389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700754765476824508382259 2551132148215236762573389)
              ·
                refine ⟨956674555580713785965021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2551132148215236762573389 956674555580713785965021)
                ·
                  refine ⟨358752958342767669736883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956674555580713785965021 358752958342767669736883)
                  ·
                    rfl

theorem cell21_1572005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_1572005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572005 prefixEnd_1572005 := by exact prefixLift 1572005
  have htrace : WordTrace (prefixWord ++ tailWord_1572005) baseStart_1572005 baseEnd_1572005 := by
    simpa [prefixWord, tailWord_1572005, baseEnd_1572005] using wordTrace_append hprefix tailTrace_1572005
  have hstable : (prefixWord ++ tailWord_1572005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572005).length < 2 ^ (prefixWord ++ tailWord_1572005).sum := by decide
  have hdescent : baseEnd_1572005 < baseStart_1572005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572033 : List Nat := [1, 2, 6, 1, 1, 1, 1, 8]
def baseStart_1572033 : Nat := 118140960795 + 1572033 * 2 ^ 59
def prefixEnd_1572033 : Nat := 4983230072969 + 3 ^ 40 * 1572033 * 2
def baseEnd_1572033 : Nat := 119586449441415281090053

theorem tailTrace_1572033 : CollatzResearch.WordTrace tailWord_1572033 prefixEnd_1572033 119586449441415281090053 := by
  unfold tailWord_1572033
  simp only [CollatzResearch.WordTrace]
  refine ⟨57336753913800397706576753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38224502609200265137717835 57336753913800397706576753)
  ·
    refine ⟨43002565435350298279932565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57336753913800397706576753 43002565435350298279932565)
    ·
      refine ⟨2015745254782045231871839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43002565435350298279932565 2015745254782045231871839)
      ·
        refine ⟨3023617882173067847807759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015745254782045231871839 3023617882173067847807759)
        ·
          refine ⟨4535426823259601771711639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023617882173067847807759 4535426823259601771711639)
          ·
            refine ⟨6803140234889402657567459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535426823259601771711639 6803140234889402657567459)
            ·
              refine ⟨10204710352334103986351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803140234889402657567459 10204710352334103986351189)
              ·
                refine ⟨119586449441415281090053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10204710352334103986351189 119586449441415281090053)
                ·
                  rfl

theorem cell21_1572033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 8].length) (baseStart_1572033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572033 prefixEnd_1572033 := by exact prefixLift 1572033
  have htrace : WordTrace (prefixWord ++ tailWord_1572033) baseStart_1572033 baseEnd_1572033 := by
    simpa [prefixWord, tailWord_1572033, baseEnd_1572033] using wordTrace_append hprefix tailTrace_1572033
  have hstable : (prefixWord ++ tailWord_1572033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572033).length < 2 ^ (prefixWord ++ tailWord_1572033).sum := by decide
  have hdescent : baseEnd_1572033 < baseStart_1572033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572075 : List Nat := [1, 1, 1, 1, 2, 15]
def baseStart_1572075 : Nat := 118140960795 + 1572075 * 2 ^ 59
def prefixEnd_1572075 : Nat := 4983230072969 + 3 ^ 40 * 1572075 * 2
def baseEnd_1572075 : Nat := 13287738270239374206299

theorem tailTrace_1572075 : CollatzResearch.WordTrace tailWord_1572075 prefixEnd_1572075 13287738270239374206299 := by
  unfold tailWord_1572075
  simp only [CollatzResearch.WordTrace]
  refine ⟨57338285779648238879605679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38225523853098825919737119 57338285779648238879605679)
  ·
    refine ⟨86007428669472358319408519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57338285779648238879605679 86007428669472358319408519)
    ·
      refine ⟨129011143004208537479112779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86007428669472358319408519 129011143004208537479112779)
      ·
        refine ⟨193516714506312806218669169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129011143004208537479112779 193516714506312806218669169)
        ·
          refine ⟨145137535879734604664001877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193516714506312806218669169 145137535879734604664001877)
          ·
            refine ⟨13287738270239374206299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 145137535879734604664001877 13287738270239374206299)
            ·
              rfl

theorem cell21_1572075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 15].length) (baseStart_1572075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572075 prefixEnd_1572075 := by exact prefixLift 1572075
  have htrace : WordTrace (prefixWord ++ tailWord_1572075) baseStart_1572075 baseEnd_1572075 := by
    simpa [prefixWord, tailWord_1572075, baseEnd_1572075] using wordTrace_append hprefix tailTrace_1572075
  have hstable : (prefixWord ++ tailWord_1572075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572075).length < 2 ^ (prefixWord ++ tailWord_1572075).sum := by decide
  have hdescent : baseEnd_1572075 < baseStart_1572075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572078 : List Nat := [4, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1572078 : Nat := 118140960795 + 1572078 * 2 ^ 59
def prefixEnd_1572078 : Nat := 4983230072969 + 3 ^ 40 * 1572078 * 2
def baseEnd_1572078 : Nat := 358769617937335765020067

theorem tailTrace_1572078 : CollatzResearch.WordTrace tailWord_1572078 prefixEnd_1572078 358769617937335765020067 := by
  unfold tailWord_1572078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167299399829671298995611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38225596799091580261309925 7167299399829671298995611)
  ·
    refine ⟨10750949099744506948493417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7167299399829671298995611 10750949099744506948493417)
    ·
      refine ⟨8063211824808380211370063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10750949099744506948493417 8063211824808380211370063)
      ·
        refine ⟨12094817737212570317055095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063211824808380211370063 12094817737212570317055095)
        ·
          refine ⟨18142226605818855475582643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12094817737212570317055095 18142226605818855475582643)
          ·
            refine ⟨27213339908728283213373965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18142226605818855475582643 27213339908728283213373965)
            ·
              refine ⟨10205002465773106205015237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27213339908728283213373965 10205002465773106205015237)
              ·
                refine ⟨1913437962332457413440357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10205002465773106205015237 1913437962332457413440357)
                ·
                  refine ⟨358769617937335765020067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913437962332457413440357 358769617937335765020067)
                  ·
                    rfl

theorem cell21_1572078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1572078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572078 prefixEnd_1572078 := by exact prefixLift 1572078
  have htrace : WordTrace (prefixWord ++ tailWord_1572078) baseStart_1572078 baseEnd_1572078 := by
    simpa [prefixWord, tailWord_1572078, baseEnd_1572078] using wordTrace_append hprefix tailTrace_1572078
  have hstable : (prefixWord ++ tailWord_1572078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572078).length < 2 ^ (prefixWord ++ tailWord_1572078).sum := by decide
  have hdescent : baseEnd_1572078 < baseStart_1572078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572084 : List Nat := [2, 6, 1, 2, 1, 2, 1, 6]
def baseStart_1572084 : Nat := 118140960795 + 1572084 * 2 ^ 59
def prefixEnd_1572084 : Nat := 4983230072969 + 3 ^ 40 * 1572084 * 2
def baseEnd_1572084 : Nat := 119590329073027029306685

theorem tailTrace_1572084 : CollatzResearch.WordTrace tailWord_1572084 prefixEnd_1572084 119590329073027029306685 := by
  unfold tailWord_1572084
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669307018307816708341653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38225742691077088944455537 28669307018307816708341653)
  ·
    refine ⟨1343873766483178908203515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28669307018307816708341653 1343873766483178908203515)
    ·
      refine ⟨2015810649724768362305273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343873766483178908203515 2015810649724768362305273)
      ·
        refine ⟨1511857987293576271728955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015810649724768362305273 1511857987293576271728955)
        ·
          refine ⟨2267786980940364407593433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511857987293576271728955 2267786980940364407593433)
          ·
            refine ⟨1700840235705273305695075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267786980940364407593433 1700840235705273305695075)
            ·
              refine ⟨2551260353557909958542613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700840235705273305695075 2551260353557909958542613)
              ·
                refine ⟨119590329073027029306685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2551260353557909958542613 119590329073027029306685)
                ·
                  rfl

theorem cell21_1572084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_1572084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572084 prefixEnd_1572084 := by exact prefixLift 1572084
  have htrace : WordTrace (prefixWord ++ tailWord_1572084) baseStart_1572084 baseEnd_1572084 := by
    simpa [prefixWord, tailWord_1572084, baseEnd_1572084] using wordTrace_append hprefix tailTrace_1572084
  have hstable : (prefixWord ++ tailWord_1572084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572084).length < 2 ^ (prefixWord ++ tailWord_1572084).sum := by decide
  have hdescent : baseEnd_1572084 < baseStart_1572084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572126 : List Nat := [4, 3, 2, 1, 2, 1, 8]
def baseStart_1572126 : Nat := 118140960795 + 1572126 * 2 ^ 59
def prefixEnd_1572126 : Nat := 4983230072969 + 3 ^ 40 * 1572126 * 2
def baseEnd_1572126 : Nat := 39864508021255372024441

theorem tailTrace_1572126 : CollatzResearch.WordTrace tailWord_1572126 prefixEnd_1572126 39864508021255372024441 := by
  unfold tailWord_1572126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7167518237807934323714029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38226763934975649726474821 7167518237807934323714029)
  ·
    refine ⟨2687819339177975371392761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7167518237807934323714029 2687819339177975371392761)
    ·
      refine ⟨2015864504383481528544571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2687819339177975371392761 2015864504383481528544571)
      ·
        refine ⟨3023796756575222292816857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2015864504383481528544571 3023796756575222292816857)
        ·
          refine ⟨2267847567431416719612643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023796756575222292816857 2267847567431416719612643)
          ·
            refine ⟨3401771351147125079418965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267847567431416719612643 3401771351147125079418965)
            ·
              refine ⟨39864508021255372024441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3401771351147125079418965 39864508021255372024441)
              ·
                rfl

theorem cell21_1572126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 8].length) (baseStart_1572126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572126 prefixEnd_1572126 := by exact prefixLift 1572126
  have htrace : WordTrace (prefixWord ++ tailWord_1572126) baseStart_1572126 baseEnd_1572126 := by
    simpa [prefixWord, tailWord_1572126, baseEnd_1572126] using wordTrace_append hprefix tailTrace_1572126
  have hstable : (prefixWord ++ tailWord_1572126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572126).length < 2 ^ (prefixWord ++ tailWord_1572126).sum := by decide
  have hdescent : baseEnd_1572126 < baseStart_1572126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572244 : List Nat := [2, 4, 2, 1, 2, 10]
def baseStart_1572244 : Nat := 118140960795 + 1572244 * 2 ^ 59
def prefixEnd_1572244 : Nat := 4983230072969 + 3 ^ 40 * 1572244 * 2
def baseEnd_1572244 : Nat := 13289166718479865379743

theorem tailTrace_1572244 : CollatzResearch.WordTrace tailWord_1572244 prefixEnd_1572244 13289166718479865379743 := by
  unfold tailWord_1572244
  simp only [CollatzResearch.WordTrace]
  refine ⟨28672224858017990371253893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38229633144023987161671857 28672224858017990371253893)
  ·
    refine ⟨5376042160878373194610105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28672224858017990371253893 5376042160878373194610105)
    ·
      refine ⟨4032031620658779895957579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5376042160878373194610105 4032031620658779895957579)
      ·
        refine ⟨6048047430988169843936369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032031620658779895957579 6048047430988169843936369)
        ·
          refine ⟨4536035573241127382952277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048047430988169843936369 4536035573241127382952277)
          ·
            refine ⟨13289166718479865379743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4536035573241127382952277 13289166718479865379743)
            ·
              rfl

theorem cell21_1572244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 10].length) (baseStart_1572244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572244 prefixEnd_1572244 := by exact prefixLift 1572244
  have htrace : WordTrace (prefixWord ++ tailWord_1572244) baseStart_1572244 baseEnd_1572244 := by
    simpa [prefixWord, tailWord_1572244, baseEnd_1572244] using wordTrace_append hprefix tailTrace_1572244
  have hstable : (prefixWord ++ tailWord_1572244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572244).length < 2 ^ (prefixWord ++ tailWord_1572244).sum := by decide
  have hdescent : baseEnd_1572244 < baseStart_1572244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572323 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 4]
def baseStart_1572323 : Nat := 118140960795 + 1572323 * 2 ^ 59
def prefixEnd_1572323 : Nat := 4983230072969 + 3 ^ 40 * 1572323 * 2
def baseEnd_1572323 : Nat := 358825530275269783436233

theorem tailTrace_1572323 : CollatzResearch.WordTrace tailWord_1572323 prefixEnd_1572323 358825530275269783436233 := by
  unfold tailWord_1572323
  simp only [CollatzResearch.WordTrace]
  refine ⟨57347331082749777234633623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38231554055166518156422415 57347331082749777234633623)
  ·
    refine ⟨86020996624124665851950435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57347331082749777234633623 86020996624124665851950435)
    ·
      refine ⟨129031494936186998777925653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86020996624124665851950435 129031494936186998777925653)
      ·
        refine ⟨6048351325133765567715265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129031494936186998777925653 6048351325133765567715265)
        ·
          refine ⟨4536263493850324175786449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6048351325133765567715265 4536263493850324175786449)
          ·
            refine ⟨3402197620387743131839837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4536263493850324175786449 3402197620387743131839837)
            ·
              refine ⟨1275824107645403674439939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3402197620387743131839837 1275824107645403674439939)
              ·
                refine ⟨1913736161468105511659909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275824107645403674439939 1913736161468105511659909)
                ·
                  refine ⟨358825530275269783436233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1913736161468105511659909 358825530275269783436233)
                  ·
                    rfl

theorem cell21_1572323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_1572323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572323 prefixEnd_1572323 := by exact prefixLift 1572323
  have htrace : WordTrace (prefixWord ++ tailWord_1572323) baseStart_1572323 baseEnd_1572323 := by
    simpa [prefixWord, tailWord_1572323, baseEnd_1572323] using wordTrace_append hprefix tailTrace_1572323
  have hstable : (prefixWord ++ tailWord_1572323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572323).length < 2 ^ (prefixWord ++ tailWord_1572323).sum := by decide
  have hdescent : baseEnd_1572323 < baseStart_1572323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572337 : List Nat := [1, 2, 2, 2, 3, 4, 2, 5]
def baseStart_1572337 : Nat := 118140960795 + 1572337 * 2 ^ 59
def prefixEnd_1572337 : Nat := 4983230072969 + 3 ^ 40 * 1572337 * 2
def baseEnd_1572337 : Nat := 119609575088669623400957

theorem tailTrace_1572337 : CollatzResearch.WordTrace tailWord_1572337 prefixEnd_1572337 119609575088669623400957 := by
  unfold tailWord_1572337
  simp only [CollatzResearch.WordTrace]
  refine ⟨57347841704699057625643265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38231894469799371750428843 57347841704699057625643265)
  ·
    refine ⟨43010881278524293219232449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57347841704699057625643265 43010881278524293219232449)
    ·
      refine ⟨32258160958893219914424337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43010881278524293219232449 32258160958893219914424337)
      ·
        refine ⟨24193620719169914935818253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32258160958893219914424337 24193620719169914935818253)
        ·
          refine ⟨9072607769688718100931845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24193620719169914935818253 9072607769688718100931845)
          ·
            refine ⟨1701113956816634643924721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9072607769688718100931845 1701113956816634643924721)
            ·
              refine ⟨1275835467612475982943541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701113956816634643924721 1275835467612475982943541)
              ·
                refine ⟨119609575088669623400957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1275835467612475982943541 119609575088669623400957)
                ·
                  rfl

theorem cell21_1572337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].length) (baseStart_1572337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572337 prefixEnd_1572337 := by exact prefixLift 1572337
  have htrace : WordTrace (prefixWord ++ tailWord_1572337) baseStart_1572337 baseEnd_1572337 := by
    simpa [prefixWord, tailWord_1572337, baseEnd_1572337] using wordTrace_append hprefix tailTrace_1572337
  have hstable : (prefixWord ++ tailWord_1572337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572337).length < 2 ^ (prefixWord ++ tailWord_1572337).sum := by decide
  have hdescent : baseEnd_1572337 < baseStart_1572337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 3]
def baseStart_1572351 : Nat := 118140960795 + 1572351 * 2 ^ 59
def prefixEnd_1572351 : Nat := 4983230072969 + 3 ^ 40 * 1572351 * 2
def baseEnd_1572351 : Nat := 358831920256747956969509

theorem tailTrace_1572351 : CollatzResearch.WordTrace tailWord_1572351 prefixEnd_1572351 358831920256747956969509 := by
  unfold tailWord_1572351
  simp only [CollatzResearch.WordTrace]
  refine ⟨57348352326648338016652907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38232234884432225344435271 57348352326648338016652907)
  ·
    refine ⟨86022528489972507024979361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57348352326648338016652907 86022528489972507024979361)
    ·
      refine ⟨64516896367479380268734521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86022528489972507024979361 64516896367479380268734521)
      ·
        refine ⟨48387672275609535201550891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64516896367479380268734521 48387672275609535201550891)
        ·
          refine ⟨72581508413414302802326337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48387672275609535201550891 72581508413414302802326337)
          ·
            refine ⟨54436131310060727101744753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72581508413414302802326337 54436131310060727101744753)
            ·
              refine ⟨40827098482545545326308565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54436131310060727101744753 40827098482545545326308565)
              ·
                refine ⟨956885120684661218585357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40827098482545545326308565 956885120684661218585357)
                ·
                  refine ⟨358831920256747956969509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956885120684661218585357 358831920256747956969509)
                  ·
                    rfl

theorem cell21_1572351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].length) (baseStart_1572351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572351 prefixEnd_1572351 := by exact prefixLift 1572351
  have htrace : WordTrace (prefixWord ++ tailWord_1572351) baseStart_1572351 baseEnd_1572351 := by
    simpa [prefixWord, tailWord_1572351, baseEnd_1572351] using wordTrace_append hprefix tailTrace_1572351
  have hstable : (prefixWord ++ tailWord_1572351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572351).length < 2 ^ (prefixWord ++ tailWord_1572351).sum := by decide
  have hdescent : baseEnd_1572351 < baseStart_1572351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572455 : List Nat := [1, 1, 5, 1, 1, 1, 2, 9]
def baseStart_1572455 : Nat := 118140960795 + 1572455 * 2 ^ 59
def prefixEnd_1572455 : Nat := 4983230072969 + 3 ^ 40 * 1572455 * 2
def baseEnd_1572455 : Nat := 119618551491222295745321

theorem tailTrace_1572455 : CollatzResearch.WordTrace tailWord_1572455 prefixEnd_1572455 119618551491222295745321 := by
  unfold tailWord_1572455
  simp only [CollatzResearch.WordTrace]
  refine ⟨57352145518271563778438819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38234763678847709185625879 57352145518271563778438819)
  ·
    refine ⟨86028218277407345667658229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57352145518271563778438819 86028218277407345667658229)
    ·
      refine ⟨8065145463506938656342959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86028218277407345667658229 8065145463506938656342959)
      ·
        refine ⟨12097718195260407984514439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065145463506938656342959 12097718195260407984514439)
        ·
          refine ⟨18146577292890611976771659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12097718195260407984514439 18146577292890611976771659)
          ·
            refine ⟨27219865939335917965157489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18146577292890611976771659 27219865939335917965157489)
            ·
              refine ⟨20414899454501938473868117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27219865939335917965157489 20414899454501938473868117)
              ·
                refine ⟨119618551491222295745321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20414899454501938473868117 119618551491222295745321)
                ·
                  rfl

theorem cell21_1572455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_1572455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572455 prefixEnd_1572455 := by exact prefixLift 1572455
  have htrace : WordTrace (prefixWord ++ tailWord_1572455) baseStart_1572455 baseEnd_1572455 := by
    simpa [prefixWord, tailWord_1572455, baseEnd_1572455] using wordTrace_append hprefix tailTrace_1572455
  have hstable : (prefixWord ++ tailWord_1572455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572455).length < 2 ^ (prefixWord ++ tailWord_1572455).sum := by decide
  have hdescent : baseEnd_1572455 < baseStart_1572455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572461 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1572461 : Nat := 118140960795 + 1572461 * 2 ^ 59
def prefixEnd_1572461 : Nat := 4983230072969 + 3 ^ 40 * 1572461 * 2
def baseEnd_1572461 : Nat := 358857023755412210135951

theorem tailTrace_1572461 : CollatzResearch.WordTrace tailWord_1572461 prefixEnd_1572461 358857023755412210135951 := by
  unfold tailWord_1572461
  simp only [CollatzResearch.WordTrace]
  refine ⟨57352364356249826803157237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38234909570833217868771491 57352364356249826803157237)
  ·
    refine ⟨5376784158398421262795991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57352364356249826803157237 5376784158398421262795991)
    ·
      refine ⟨8065176237597631894193987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376784158398421262795991 8065176237597631894193987)
      ·
        refine ⟨12097764356396447841290981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065176237597631894193987 12097764356396447841290981)
        ·
          refine ⟨2268330816824333970242059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12097764356396447841290981 2268330816824333970242059)
          ·
            refine ⟨3402496225236500955363089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268330816824333970242059 3402496225236500955363089)
            ·
              refine ⟨2551872168927375716522317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3402496225236500955363089 2551872168927375716522317)
              ·
                refine ⟨956952063347765893695869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2551872168927375716522317 956952063347765893695869)
                ·
                  refine ⟨358857023755412210135951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 956952063347765893695869 358857023755412210135951)
                  ·
                    rfl

theorem cell21_1572461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1572461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572461 prefixEnd_1572461 := by exact prefixLift 1572461
  have htrace : WordTrace (prefixWord ++ tailWord_1572461) baseStart_1572461 baseEnd_1572461 := by
    simpa [prefixWord, tailWord_1572461, baseEnd_1572461] using wordTrace_append hprefix tailTrace_1572461
  have hstable : (prefixWord ++ tailWord_1572461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572461).length < 2 ^ (prefixWord ++ tailWord_1572461).sum := by decide
  have hdescent : baseEnd_1572461 < baseStart_1572461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572548 : List Nat := [2, 3, 3, 1, 1, 1, 4, 6]
def baseStart_1572548 : Nat := 118140960795 + 1572548 * 2 ^ 59
def prefixEnd_1572548 : Nat := 4983230072969 + 3 ^ 40 * 1572548 * 2
def baseEnd_1572548 : Nat := 119625626113573130728591

theorem tailTrace_1572548 : CollatzResearch.WordTrace tailWord_1572548 prefixEnd_1572548 119625626113573130728591 := by
  unfold tailWord_1572548
  simp only [CollatzResearch.WordTrace]
  refine ⟨28677768753467320330787149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38237025004623093774382865 28677768753467320330787149)
  ·
    refine ⟨10754163282550245124045181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28677768753467320330787149 10754163282550245124045181)
    ·
      refine ⟨4032811230956341921516943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10754163282550245124045181 4032811230956341921516943)
      ·
        refine ⟨6049216846434512882275415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032811230956341921516943 6049216846434512882275415)
        ·
          refine ⟨9073825269651769323413123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049216846434512882275415 9073825269651769323413123)
          ·
            refine ⟨13610737904477653985119685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9073825269651769323413123 13610737904477653985119685)
            ·
              refine ⟨2552013357089560122209941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13610737904477653985119685 2552013357089560122209941)
              ·
                refine ⟨119625626113573130728591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2552013357089560122209941 119625626113573130728591)
                ·
                  rfl

theorem cell21_1572548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 6].length) (baseStart_1572548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572548 prefixEnd_1572548 := by exact prefixLift 1572548
  have htrace : WordTrace (prefixWord ++ tailWord_1572548) baseStart_1572548 baseEnd_1572548 := by
    simpa [prefixWord, tailWord_1572548, baseEnd_1572548] using wordTrace_append hprefix tailTrace_1572548
  have hstable : (prefixWord ++ tailWord_1572548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572548).length < 2 ^ (prefixWord ++ tailWord_1572548).sum := by decide
  have hdescent : baseEnd_1572548 < baseStart_1572548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572576 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1572576 : Nat := 118140960795 + 1572576 * 2 ^ 59
def prefixEnd_1572576 : Nat := 4983230072969 + 3 ^ 40 * 1572576 * 2
def baseEnd_1572576 : Nat := 358883268322197565719049

theorem tailTrace_1572576 : CollatzResearch.WordTrace tailWord_1572576 prefixEnd_1572576 358883268322197565719049 := by
  unfold tailWord_1572576
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678279375416600721796791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38237705833888800962395721 28678279375416600721796791)
  ·
    refine ⟨43017419063124901082695187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28678279375416600721796791 43017419063124901082695187)
    ·
      refine ⟨64526128594687351624042781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43017419063124901082695187 64526128594687351624042781)
      ·
        refine ⟨24197298223007756859016043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64526128594687351624042781 24197298223007756859016043)
        ·
          refine ⟨36295947334511635288524065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24197298223007756859016043 36295947334511635288524065)
          ·
            refine ⟨27221960500883726466393049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36295947334511635288524065 27221960500883726466393049)
            ·
              refine ⟨20416470375662794849794787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27221960500883726466393049 20416470375662794849794787)
              ·
                refine ⟨30624705563494192274692181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20416470375662794849794787 30624705563494192274692181)
                ·
                  refine ⟨358883268322197565719049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30624705563494192274692181 358883268322197565719049)
                  ·
                    rfl

theorem cell21_1572576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1572576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572576 prefixEnd_1572576 := by exact prefixLift 1572576
  have htrace : WordTrace (prefixWord ++ tailWord_1572576) baseStart_1572576 baseEnd_1572576 := by
    simpa [prefixWord, tailWord_1572576, baseEnd_1572576] using wordTrace_append hprefix tailTrace_1572576
  have hstable : (prefixWord ++ tailWord_1572576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572576).length < 2 ^ (prefixWord ++ tailWord_1572576).sum := by decide
  have hdescent : baseEnd_1572576 < baseStart_1572576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572593 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_1572593 : Nat := 118140960795 + 1572593 * 2 ^ 59
def prefixEnd_1572593 : Nat := 4983230072969 + 3 ^ 40 * 1572593 * 2
def baseEnd_1572593 : Nat := 358887147953809313935681

theorem tailTrace_1572593 : CollatzResearch.WordTrace tailWord_1572593 prefixEnd_1572593 358887147953809313935681 := by
  unfold tailWord_1572593
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357178791771613346962433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38238119194514408897974955 57357178791771613346962433)
  ·
    refine ⟨43017884093828710010221825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57357178791771613346962433 43017884093828710010221825)
    ·
      refine ⟨32263413070371532507666369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43017884093828710010221825 32263413070371532507666369)
      ·
        refine ⟨24197559802778649380749777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32263413070371532507666369 24197559802778649380749777)
        ·
          refine ⟨18148169852083987035562333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24197559802778649380749777 18148169852083987035562333)
          ·
            refine ⟨6805563694531495138335875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18148169852083987035562333 6805563694531495138335875)
            ·
              refine ⟨10208345541797242707503813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805563694531495138335875 10208345541797242707503813)
              ·
                refine ⟨1914064789086983007656965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10208345541797242707503813 1914064789086983007656965)
                ·
                  refine ⟨358887147953809313935681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914064789086983007656965 358887147953809313935681)
                  ·
                    rfl

theorem cell21_1572593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_1572593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572593 prefixEnd_1572593 := by exact prefixLift 1572593
  have htrace : WordTrace (prefixWord ++ tailWord_1572593) baseStart_1572593 baseEnd_1572593 := by
    simpa [prefixWord, tailWord_1572593, baseEnd_1572593] using wordTrace_append hprefix tailTrace_1572593
  have hstable : (prefixWord ++ tailWord_1572593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572593).length < 2 ^ (prefixWord ++ tailWord_1572593).sum := by decide
  have hdescent : baseEnd_1572593 < baseStart_1572593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572607 : List Nat := [1, 1, 2, 2, 1, 3, 5, 6]
def baseStart_1572607 : Nat := 118140960795 + 1572607 * 2 ^ 59
def prefixEnd_1572607 : Nat := 4983230072969 + 3 ^ 40 * 1572607 * 2
def baseEnd_1572607 : Nat := 119630114314849466900773

theorem tailTrace_1572607 : CollatzResearch.WordTrace tailWord_1572607 prefixEnd_1572607 119630114314849466900773 := by
  unfold tailWord_1572607
  simp only [CollatzResearch.WordTrace]
  refine ⟨57357689413720893737972075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38238459609147262491981383 57357689413720893737972075)
  ·
    refine ⟨86036534120581340606958113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57357689413720893737972075 86036534120581340606958113)
    ·
      refine ⟨64527400590436005455218585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86036534120581340606958113 64527400590436005455218585)
      ·
        refine ⟨48395550442827004091413939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64527400590436005455218585 48395550442827004091413939)
        ·
          refine ⟨72593325664240506137120909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48395550442827004091413939 72593325664240506137120909)
          ·
            refine ⟨27222497124090189801420341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72593325664240506137120909 27222497124090189801420341)
            ·
              refine ⟨2552109105383455293883157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27222497124090189801420341 2552109105383455293883157)
              ·
                refine ⟨119630114314849466900773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2552109105383455293883157 119630114314849466900773)
                ·
                  rfl

theorem cell21_1572607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_1572607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572607 prefixEnd_1572607 := by exact prefixLift 1572607
  have htrace : WordTrace (prefixWord ++ tailWord_1572607) baseStart_1572607 baseEnd_1572607 := by
    simpa [prefixWord, tailWord_1572607, baseEnd_1572607] using wordTrace_append hprefix tailTrace_1572607
  have hstable : (prefixWord ++ tailWord_1572607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572607).length < 2 ^ (prefixWord ++ tailWord_1572607).sum := by decide
  have hdescent : baseEnd_1572607 < baseStart_1572607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572610 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1572610 : Nat := 118140960795 + 1572610 * 2 ^ 59
def prefixEnd_1572610 : Nat := 4983230072969 + 3 ^ 40 * 1572610 * 2
def baseEnd_1572610 : Nat := 358891027585421062152313

theorem tailTrace_1572610 : CollatzResearch.WordTrace tailWord_1572610 prefixEnd_1572610 358891027585421062152313 := by
  unfold tailWord_1572610
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339449708177506312582821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38238532555140016833554189 14339449708177506312582821)
  ·
    refine ⟨2688646820283282433609279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14339449708177506312582821 2688646820283282433609279)
    ·
      refine ⟨4032970230424923650413919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688646820283282433609279 4032970230424923650413919)
      ·
        refine ⟨6049455345637385475620879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032970230424923650413919 6049455345637385475620879)
        ·
          refine ⟨9074183018456078213431319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049455345637385475620879 9074183018456078213431319)
          ·
            refine ⟨13611274527684117320146979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074183018456078213431319 13611274527684117320146979)
            ·
              refine ⟨20416911791526175980220469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611274527684117320146979 20416911791526175980220469)
              ·
                refine ⟨1914085480455578998145669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20416911791526175980220469 1914085480455578998145669)
                ·
                  refine ⟨358891027585421062152313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914085480455578998145669 358891027585421062152313)
                  ·
                    rfl

theorem cell21_1572610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1572610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572610 prefixEnd_1572610 := by exact prefixLift 1572610
  have htrace : WordTrace (prefixWord ++ tailWord_1572610) baseStart_1572610 baseEnd_1572610 := by
    simpa [prefixWord, tailWord_1572610, baseEnd_1572610] using wordTrace_append hprefix tailTrace_1572610
  have hstable : (prefixWord ++ tailWord_1572610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572610).length < 2 ^ (prefixWord ++ tailWord_1572610).sum := by decide
  have hdescent : baseEnd_1572610 < baseStart_1572610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572762 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1572762 : Nat := 118140960795 + 1572762 * 2 ^ 59
def prefixEnd_1572762 : Nat := 4983230072969 + 3 ^ 40 * 1572762 * 2
def baseEnd_1572762 : Nat := 358925716056302575618669

theorem tailTrace_1572762 : CollatzResearch.WordTrace tailWord_1572762 prefixEnd_1572762 358925716056302575618669 := by
  unfold tailWord_1572762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340835682039838802466135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38242228485439570139909693 14340835682039838802466135)
  ·
    refine ⟨21511253523059758203699203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14340835682039838802466135 21511253523059758203699203)
    ·
      refine ⟨32266880284589637305548805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21511253523059758203699203 32266880284589637305548805)
      ·
        refine ⟨6050040053360556994790401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32266880284589637305548805 6050040053360556994790401)
        ·
          refine ⟨4537530040020417746092801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050040053360556994790401 4537530040020417746092801)
          ·
            refine ⟨3403147530015313309569601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537530040020417746092801 3403147530015313309569601)
            ·
              refine ⟨2552360647511484982177201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403147530015313309569601 2552360647511484982177201)
              ·
                refine ⟨1914270485633613736632901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552360647511484982177201 1914270485633613736632901)
                ·
                  refine ⟨358925716056302575618669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1914270485633613736632901 358925716056302575618669)
                  ·
                    rfl

theorem cell21_1572762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1572762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572762 prefixEnd_1572762 := by exact prefixLift 1572762
  have htrace : WordTrace (prefixWord ++ tailWord_1572762) baseStart_1572762 baseEnd_1572762 := by
    simpa [prefixWord, tailWord_1572762, baseEnd_1572762] using wordTrace_append hprefix tailTrace_1572762
  have hstable : (prefixWord ++ tailWord_1572762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572762).length < 2 ^ (prefixWord ++ tailWord_1572762).sum := by decide
  have hdescent : baseEnd_1572762 < baseStart_1572762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572765 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 3]
def baseStart_1572765 : Nat := 118140960795 + 1572765 * 2 ^ 59
def prefixEnd_1572765 : Nat := 4983230072969 + 3 ^ 40 * 1572765 * 2
def baseEnd_1572765 : Nat := 358926400697175237068663

theorem tailTrace_1572765 : CollatzResearch.WordTrace tailWord_1572765 prefixEnd_1572765 358926400697175237068663 := by
  unfold tailWord_1572765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57363452147148486722223749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38242301431432324481482499 57363452147148486722223749)
  ·
    refine ⟨10755647277590341260416953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57363452147148486722223749 10755647277590341260416953)
    ·
      refine ⟨8066735458192755945312715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755647277590341260416953 8066735458192755945312715)
      ·
        refine ⟨12100103187289133917969073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066735458192755945312715 12100103187289133917969073)
        ·
          refine ⟨9075077390466850438476805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12100103187289133917969073 9075077390466850438476805)
          ·
            refine ⟨1701577010712534457214401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9075077390466850438476805 1701577010712534457214401)
            ·
              refine ⟨1276182758034400842910801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701577010712534457214401 1276182758034400842910801)
              ·
                refine ⟨957137068525800632183101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276182758034400842910801 957137068525800632183101)
                ·
                  refine ⟨358926400697175237068663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957137068525800632183101 358926400697175237068663)
                  ·
                    rfl

theorem cell21_1572765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_1572765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572765 prefixEnd_1572765 := by exact prefixLift 1572765
  have htrace : WordTrace (prefixWord ++ tailWord_1572765) baseStart_1572765 baseEnd_1572765 := by
    simpa [prefixWord, tailWord_1572765, baseEnd_1572765] using wordTrace_append hprefix tailTrace_1572765
  have hstable : (prefixWord ++ tailWord_1572765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572765).length < 2 ^ (prefixWord ++ tailWord_1572765).sum := by decide
  have hdescent : baseEnd_1572765 < baseStart_1572765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572773 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_1572773 : Nat := 118140960795 + 1572773 * 2 ^ 59
def prefixEnd_1572773 : Nat := 4983230072969 + 3 ^ 40 * 1572773 * 2
def baseEnd_1572773 : Nat := 358928226406169000935313

theorem tailTrace_1572773 : CollatzResearch.WordTrace tailWord_1572773 prefixEnd_1572773 358928226406169000935313 := by
  unfold tailWord_1572773
  simp only [CollatzResearch.WordTrace]
  refine ⟨57363743931119504088514973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38242495954079669392343315 57363743931119504088514973)
  ·
    refine ⟨21511403974169814033193115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57363743931119504088514973 21511403974169814033193115)
    ·
      refine ⟨32267105961254721049789673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21511403974169814033193115 32267105961254721049789673)
      ·
        refine ⟨24200329470941040787342255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32267105961254721049789673 24200329470941040787342255)
        ·
          refine ⟨36300494206411561181013383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24200329470941040787342255 36300494206411561181013383)
          ·
            refine ⟨54450741309617341771520075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36300494206411561181013383 54450741309617341771520075)
            ·
              refine ⟨81676111964426012657280113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54450741309617341771520075 81676111964426012657280113)
              ·
                refine ⟨61257083973319509492960085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81676111964426012657280113 61257083973319509492960085)
                ·
                  refine ⟨358928226406169000935313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61257083973319509492960085 358928226406169000935313)
                  ·
                    rfl

theorem cell21_1572773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_1572773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572773 prefixEnd_1572773 := by exact prefixLift 1572773
  have htrace : WordTrace (prefixWord ++ tailWord_1572773) baseStart_1572773 baseEnd_1572773 := by
    simpa [prefixWord, tailWord_1572773, baseEnd_1572773] using wordTrace_append hprefix tailTrace_1572773
  have hstable : (prefixWord ++ tailWord_1572773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572773).length < 2 ^ (prefixWord ++ tailWord_1572773).sum := by decide
  have hdescent : baseEnd_1572773 < baseStart_1572773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572821 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_1572821 : Nat := 118140960795 + 1572821 * 2 ^ 59
def prefixEnd_1572821 : Nat := 4983230072969 + 3 ^ 40 * 1572821 * 2
def baseEnd_1572821 : Nat := 358939180660131584135215

theorem tailTrace_1572821 : CollatzResearch.WordTrace tailWord_1572821 prefixEnd_1572821 358939180660131584135215 := by
  unfold tailWord_1572821
  simp only [CollatzResearch.WordTrace]
  refine ⟨57365494634945608286262317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38243663089963738857508211 57365494634945608286262317)
  ·
    refine ⟨21512060488104603107348369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57365494634945608286262317 21512060488104603107348369)
    ·
      refine ⟨16134045366078452330511277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21512060488104603107348369 16134045366078452330511277)
      ·
        refine ⟨6050267012279419623941729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16134045366078452330511277 6050267012279419623941729)
        ·
          refine ⟨4537700259209564717956297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050267012279419623941729 4537700259209564717956297)
          ·
            refine ⟨3403275194407173538467223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537700259209564717956297 3403275194407173538467223)
            ·
              refine ⟨5104912791610760307700835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403275194407173538467223 5104912791610760307700835)
              ·
                refine ⟨7657369187416140461551253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104912791610760307700835 7657369187416140461551253)
                ·
                  refine ⟨358939180660131584135215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7657369187416140461551253 358939180660131584135215)
                  ·
                    rfl

theorem cell21_1572821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_1572821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1572821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1572821 prefixEnd_1572821 := by exact prefixLift 1572821
  have htrace : WordTrace (prefixWord ++ tailWord_1572821) baseStart_1572821 baseEnd_1572821 := by
    simpa [prefixWord, tailWord_1572821, baseEnd_1572821] using wordTrace_append hprefix tailTrace_1572821
  have hstable : (prefixWord ++ tailWord_1572821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572821).length < 2 ^ (prefixWord ++ tailWord_1572821).sum := by decide
  have hdescent : baseEnd_1572821 < baseStart_1572821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573038 : List Nat := [4, 1, 4, 2, 2, 1, 7]
def baseStart_1573038 : Nat := 118140960795 + 1573038 * 2 ^ 59
def prefixEnd_1573038 : Nat := 4983230072969 + 3 ^ 40 * 1573038 * 2
def baseEnd_1573038 : Nat := 39887633668509714335345

theorem tailTrace_1573038 : CollatzResearch.WordTrace tailWord_1573038 prefixEnd_1573038 39887633668509714335345 := by
  unfold tailWord_1573038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171676159394931793363971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38248939516772969564607845 7171676159394931793363971)
  ·
    refine ⟨10757514239092397690045957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171676159394931793363971 10757514239092397690045957)
    ·
      refine ⟨2017033919829824566883617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10757514239092397690045957 2017033919829824566883617)
      ·
        refine ⟨1512775439872368425162713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2017033919829824566883617 1512775439872368425162713)
        ·
          refine ⟨1134581579904276318872035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512775439872368425162713 1134581579904276318872035)
          ·
            refine ⟨1701872369856414478308053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134581579904276318872035 1701872369856414478308053)
            ·
              refine ⟨39887633668509714335345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1701872369856414478308053 39887633668509714335345)
              ·
                rfl

theorem cell21_1573038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 7].length) (baseStart_1573038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573038 prefixEnd_1573038 := by exact prefixLift 1573038
  have htrace : WordTrace (prefixWord ++ tailWord_1573038) baseStart_1573038 baseEnd_1573038 := by
    simpa [prefixWord, tailWord_1573038, baseEnd_1573038] using wordTrace_append hprefix tailTrace_1573038
  have hstable : (prefixWord ++ tailWord_1573038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573038).length < 2 ^ (prefixWord ++ tailWord_1573038).sum := by decide
  have hdescent : baseEnd_1573038 < baseStart_1573038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573052 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 5]
def baseStart_1573052 : Nat := 118140960795 + 1573052 * 2 ^ 59
def prefixEnd_1573052 : Nat := 4983230072969 + 3 ^ 40 * 1573052 * 2
def baseEnd_1573052 : Nat := 358991898007326515784743

theorem tailTrace_1573052 : CollatzResearch.WordTrace tailWord_1573052 prefixEnd_1573052 358991898007326515784743 := by
  unfold tailWord_1573052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686959948554367368960705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38249279931405823158614273 28686959948554367368960705)
  ·
    refine ⟨21515219961415775526720529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28686959948554367368960705 21515219961415775526720529)
    ·
      refine ⟨16136414971061831645040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21515219961415775526720529 16136414971061831645040397)
      ·
        refine ⟨6051155614148186866890149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16136414971061831645040397 6051155614148186866890149)
        ·
          refine ⟨1134591677652785037541903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6051155614148186866890149 1134591677652785037541903)
          ·
            refine ⟨1701887516479177556312855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134591677652785037541903 1701887516479177556312855)
            ·
              refine ⟨2552831274718766334469283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701887516479177556312855 2552831274718766334469283)
              ·
                refine ⟨3829246912078149501703925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552831274718766334469283 3829246912078149501703925)
                ·
                  refine ⟨358991898007326515784743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3829246912078149501703925 358991898007326515784743)
                  ·
                    rfl

theorem cell21_1573052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_1573052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573052 prefixEnd_1573052 := by exact prefixLift 1573052
  have htrace : WordTrace (prefixWord ++ tailWord_1573052) baseStart_1573052 baseEnd_1573052 := by
    simpa [prefixWord, tailWord_1573052, baseEnd_1573052] using wordTrace_append hprefix tailTrace_1573052
  have hstable : (prefixWord ++ tailWord_1573052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573052).length < 2 ^ (prefixWord ++ tailWord_1573052).sum := by decide
  have hdescent : baseEnd_1573052 < baseStart_1573052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573159 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 6]
def baseStart_1573159 : Nat := 118140960795 + 1573159 * 2 ^ 59
def prefixEnd_1573159 : Nat := 4983230072969 + 3 ^ 40 * 1573159 * 2
def baseEnd_1573159 : Nat := 359016316865118107501191

theorem tailTrace_1573159 : CollatzResearch.WordTrace tailWord_1573159 prefixEnd_1573159 359016316865118107501191 := by
  unfold tailWord_1573159
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377822507721092012066531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38251881671814061341377687 57377822507721092012066531)
  ·
    refine ⟨86066733761581638018099797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377822507721092012066531 86066733761581638018099797)
    ·
      refine ⟨1008594536268534820524607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 86066733761581638018099797 1008594536268534820524607)
      ·
        refine ⟨1512891804402802230786911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008594536268534820524607 1512891804402802230786911)
        ·
          refine ⟨2269337706604203346180367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512891804402802230786911 2269337706604203346180367)
          ·
            refine ⟨3404006559906305019270551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269337706604203346180367 3404006559906305019270551)
            ·
              refine ⟨5106009839859457528905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404006559906305019270551 5106009839859457528905827)
              ·
                refine ⟨7659014759789186293358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106009839859457528905827 7659014759789186293358741)
                ·
                  refine ⟨359016316865118107501191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7659014759789186293358741 359016316865118107501191)
                  ·
                    rfl

theorem cell21_1573159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].length) (baseStart_1573159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573159 prefixEnd_1573159 := by exact prefixLift 1573159
  have htrace : WordTrace (prefixWord ++ tailWord_1573159) baseStart_1573159 baseEnd_1573159 := by
    simpa [prefixWord, tailWord_1573159, baseEnd_1573159] using wordTrace_append hprefix tailTrace_1573159
  have hstable : (prefixWord ++ tailWord_1573159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573159).length < 2 ^ (prefixWord ++ tailWord_1573159).sum := by decide
  have hdescent : baseEnd_1573159 < baseStart_1573159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573204 : List Nat := [2, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1573204 : Nat := 118140960795 + 1573204 * 2 ^ 59
def prefixEnd_1573204 : Nat := 4983230072969 + 3 ^ 40 * 1573204 * 2
def baseEnd_1573204 : Nat := 359026586478208029251099

theorem tailTrace_1573204 : CollatzResearch.WordTrace tailWord_1573204 prefixEnd_1573204 359026586478208029251099 := by
  unfold tailWord_1573204
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689731896279032348727333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38252975861705376464969777 28689731896279032348727333)
  ·
    refine ⟨5379324730552318565386375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28689731896279032348727333 5379324730552318565386375)
    ·
      refine ⟨8068987095828477848079563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379324730552318565386375 8068987095828477848079563)
      ·
        refine ⟨12103480643742716772119345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068987095828477848079563 12103480643742716772119345)
        ·
          refine ⟨9077610482807037579089509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12103480643742716772119345 9077610482807037579089509)
          ·
            refine ⟨1702051965526319546079283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9077610482807037579089509 1702051965526319546079283)
            ·
              refine ⟨2553077948289479319118925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702051965526319546079283 2553077948289479319118925)
              ·
                refine ⟨957404230608554744669597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2553077948289479319118925 957404230608554744669597)
                ·
                  refine ⟨359026586478208029251099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957404230608554744669597 359026586478208029251099)
                  ·
                    rfl

theorem cell21_1573204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1573204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573204 prefixEnd_1573204 := by exact prefixLift 1573204
  have htrace : WordTrace (prefixWord ++ tailWord_1573204) baseStart_1573204 baseEnd_1573204 := by
    simpa [prefixWord, tailWord_1573204, baseEnd_1573204] using wordTrace_append hprefix tailTrace_1573204
  have hstable : (prefixWord ++ tailWord_1573204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573204).length < 2 ^ (prefixWord ++ tailWord_1573204).sum := by decide
  have hdescent : baseEnd_1573204 < baseStart_1573204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573274 : List Nat := [3, 1, 1, 4, 1, 11]
def baseStart_1573274 : Nat := 118140960795 + 1573274 * 2 ^ 59
def prefixEnd_1573274 : Nat := 4983230072969 + 3 ^ 40 * 1573274 * 2
def baseEnd_1573274 : Nat := 13297872645626054188307

theorem tailTrace_1573274 : CollatzResearch.WordTrace tailWord_1573274 prefixEnd_1573274 13297872645626054188307 := by
  unfold tailWord_1573274
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345504225576116663125719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38254677934869644435001917 14345504225576116663125719)
  ·
    refine ⟨21518256338364174994688579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14345504225576116663125719 21518256338364174994688579)
    ·
      refine ⟨32277384507546262492032869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21518256338364174994688579 32277384507546262492032869)
      ·
        refine ⟨6052009595164924217256163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32277384507546262492032869 6052009595164924217256163)
        ·
          refine ⟨9078014392747386325884245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052009595164924217256163 9078014392747386325884245)
          ·
            refine ⟨13297872645626054188307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9078014392747386325884245 13297872645626054188307)
            ·
              rfl

theorem cell21_1573274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 11].length) (baseStart_1573274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573274 prefixEnd_1573274 := by exact prefixLift 1573274
  have htrace : WordTrace (prefixWord ++ tailWord_1573274) baseStart_1573274 baseEnd_1573274 := by
    simpa [prefixWord, tailWord_1573274, baseEnd_1573274] using wordTrace_append hprefix tailTrace_1573274
  have hstable : (prefixWord ++ tailWord_1573274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573274).length < 2 ^ (prefixWord ++ tailWord_1573274).sum := by decide
  have hdescent : baseEnd_1573274 < baseStart_1573274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573280 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_1573280 : Nat := 118140960795 + 1573280 * 2 ^ 59
def prefixEnd_1573280 : Nat := 4983230072969 + 3 ^ 40 * 1573280 * 2
def baseEnd_1573280 : Nat := 359043930713648785984277

theorem tailTrace_1573280 : CollatzResearch.WordTrace tailWord_1573280 prefixEnd_1573280 359043930713648785984277 := by
  unfold tailWord_1573280
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691117870141364838610647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38254823826855153118147529 28691117870141364838610647)
  ·
    refine ⟨43036676805212047257915971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28691117870141364838610647 43036676805212047257915971)
    ·
      refine ⟨64555015207818070886873957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43036676805212047257915971 64555015207818070886873957)
      ·
        refine ⟨12104065351465888291288867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64555015207818070886873957 12104065351465888291288867)
        ·
          refine ⟨18156098027198832436933301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12104065351465888291288867 18156098027198832436933301)
          ·
            refine ⟨1702134190049890540962497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18156098027198832436933301 1702134190049890540962497)
            ·
              refine ⟨1276600642537417905721873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702134190049890540962497 1276600642537417905721873)
              ·
                refine ⟨957450481903063429291405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276600642537417905721873 957450481903063429291405)
                ·
                  refine ⟨359043930713648785984277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957450481903063429291405 359043930713648785984277)
                  ·
                    rfl

theorem cell21_1573280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_1573280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573280 prefixEnd_1573280 := by exact prefixLift 1573280
  have htrace : WordTrace (prefixWord ++ tailWord_1573280) baseStart_1573280 baseEnd_1573280 := by
    simpa [prefixWord, tailWord_1573280, baseEnd_1573280] using wordTrace_append hprefix tailTrace_1573280
  have hstable : (prefixWord ++ tailWord_1573280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573280).length < 2 ^ (prefixWord ++ tailWord_1573280).sum := by decide
  have hdescent : baseEnd_1573280 < baseStart_1573280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573305 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_1573305 : Nat := 118140960795 + 1573305 * 2 ^ 59
def prefixEnd_1573305 : Nat := 4983230072969 + 3 ^ 40 * 1573305 * 2
def baseEnd_1573305 : Nat := 359049636054254298067559

theorem tailTrace_1573305 : CollatzResearch.WordTrace tailWord_1573305 prefixEnd_1573305 359049636054254298067559 := by
  unfold tailWord_1573305
  simp only [CollatzResearch.WordTrace]
  refine ⟨57383147565192158946881369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38255431710128105964587579 57383147565192158946881369)
  ·
    refine ⟨43037360673894119210161027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57383147565192158946881369 43037360673894119210161027)
    ·
      refine ⟨64556041010841178815241541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43037360673894119210161027 64556041010841178815241541)
      ·
        refine ⟨12104257689532721027857789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64556041010841178815241541 12104257689532721027857789)
        ·
          refine ⟨4539096633574770385446671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104257689532721027857789 4539096633574770385446671)
          ·
            refine ⟨6808644950362155578170007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539096633574770385446671 6808644950362155578170007)
            ·
              refine ⟨10212967425543233367255011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808644950362155578170007 10212967425543233367255011)
              ·
                refine ⟨15319451138314850050882517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10212967425543233367255011 15319451138314850050882517)
                ·
                  refine ⟨359049636054254298067559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15319451138314850050882517 359049636054254298067559)
                  ·
                    rfl

theorem cell21_1573305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_1573305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573305 prefixEnd_1573305 := by exact prefixLift 1573305
  have htrace : WordTrace (prefixWord ++ tailWord_1573305) baseStart_1573305 baseEnd_1573305 := by
    simpa [prefixWord, tailWord_1573305, baseEnd_1573305] using wordTrace_append hprefix tailTrace_1573305
  have hstable : (prefixWord ++ tailWord_1573305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573305).length < 2 ^ (prefixWord ++ tailWord_1573305).sum := by decide
  have hdescent : baseEnd_1573305 < baseStart_1573305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573308 : List Nat := [2, 2, 2, 4, 1, 2, 3, 5]
def baseStart_1573308 : Nat := 118140960795 + 1573308 * 2 ^ 59
def prefixEnd_1573308 : Nat := 4983230072969 + 3 ^ 40 * 1573308 * 2
def baseEnd_1573308 : Nat := 119683440231708986505851

theorem tailTrace_1573308 : CollatzResearch.WordTrace tailWord_1573308 prefixEnd_1573308 119683440231708986505851 := by
  unfold tailWord_1573308
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691628492090645229620289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38255504656120860306160385 28691628492090645229620289)
  ·
    refine ⟨21518721369067983922215217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28691628492090645229620289 21518721369067983922215217)
    ·
      refine ⟨16139041026800987941661413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21518721369067983922215217 16139041026800987941661413)
      ·
        refine ⟨3026070192525185239061515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16139041026800987941661413 3026070192525185239061515)
        ·
          refine ⟨4539105288787777858592273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026070192525185239061515 4539105288787777858592273)
          ·
            refine ⟨3404328966590833393944205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539105288787777858592273 3404328966590833393944205)
            ·
              refine ⟨1276623362471562522729077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3404328966590833393944205 1276623362471562522729077)
              ·
                refine ⟨119683440231708986505851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1276623362471562522729077 119683440231708986505851)
                ·
                  rfl

theorem cell21_1573308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 5].length) (baseStart_1573308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573308 prefixEnd_1573308 := by exact prefixLift 1573308
  have htrace : WordTrace (prefixWord ++ tailWord_1573308) baseStart_1573308 baseEnd_1573308 := by
    simpa [prefixWord, tailWord_1573308, baseEnd_1573308] using wordTrace_append hprefix tailTrace_1573308
  have hstable : (prefixWord ++ tailWord_1573308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573308).length < 2 ^ (prefixWord ++ tailWord_1573308).sum := by decide
  have hdescent : baseEnd_1573308 < baseStart_1573308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573395 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_1573395 : Nat := 118140960795 + 1573395 * 2 ^ 59
def prefixEnd_1573395 : Nat := 4983230072969 + 3 ^ 40 * 1573395 * 2
def baseEnd_1573395 : Nat := 359070175280434141567375

theorem tailTrace_1573395 : CollatzResearch.WordTrace tailWord_1573395 prefixEnd_1573395 359070175280434141567375 := by
  unfold tailWord_1573395
  simp only [CollatzResearch.WordTrace]
  refine ⟨57386430134866104317657639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38257620089910736211771759 57386430134866104317657639)
  ·
    refine ⟨86079645202299156476486459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57386430134866104317657639 86079645202299156476486459)
    ·
      refine ⟨129119467803448734714729689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86079645202299156476486459 129119467803448734714729689)
      ·
        refine ⟨96839600852586551036047267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129119467803448734714729689 96839600852586551036047267)
        ·
          refine ⟨145259401278879826554070901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96839600852586551036047267 145259401278879826554070901)
          ·
            refine ⟨13618068869894983739444147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145259401278879826554070901 13618068869894983739444147)
            ·
              refine ⟨20427103304842475609166221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13618068869894983739444147 20427103304842475609166221)
              ·
                refine ⟨7660163739315928353437333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20427103304842475609166221 7660163739315928353437333)
                ·
                  refine ⟨359070175280434141567375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7660163739315928353437333 359070175280434141567375)
                  ·
                    rfl

theorem cell21_1573395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_1573395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573395 prefixEnd_1573395 := by exact prefixLift 1573395
  have htrace : WordTrace (prefixWord ++ tailWord_1573395) baseStart_1573395 baseEnd_1573395 := by
    simpa [prefixWord, tailWord_1573395, baseEnd_1573395] using wordTrace_append hprefix tailTrace_1573395
  have hstable : (prefixWord ++ tailWord_1573395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573395).length < 2 ^ (prefixWord ++ tailWord_1573395).sum := by decide
  have hdescent : baseEnd_1573395 < baseStart_1573395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573426 : List Nat := [3, 2, 1, 1, 2, 1, 4, 7]
def baseStart_1573426 : Nat := 118140960795 + 1573426 * 2 ^ 59
def prefixEnd_1573426 : Nat := 4983230072969 + 3 ^ 40 * 1573426 * 2
def baseEnd_1573426 : Nat := 119692416634261658850215

theorem tailTrace_1573426 : CollatzResearch.WordTrace tailWord_1573426 prefixEnd_1573426 119692416634261658850215 := by
  unfold tailWord_1573426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346890199438449153009033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38258373865169197741357421 14346890199438449153009033)
  ·
    refine ⟨10760167649578836864756775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14346890199438449153009033 10760167649578836864756775)
    ·
      refine ⟨16140251474368255297135163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10760167649578836864756775 16140251474368255297135163)
      ·
        refine ⟨24210377211552382945702745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16140251474368255297135163 24210377211552382945702745)
        ·
          refine ⟨18157782908664287209277059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24210377211552382945702745 18157782908664287209277059)
          ·
            refine ⟨27236674362996430813915589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18157782908664287209277059 27236674362996430813915589)
            ·
              refine ⟨5106876443061830777609173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27236674362996430813915589 5106876443061830777609173)
              ·
                refine ⟨119692416634261658850215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5106876443061830777609173 119692416634261658850215)
                ·
                  rfl

theorem cell21_1573426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_1573426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573426 prefixEnd_1573426 := by exact prefixLift 1573426
  have htrace : WordTrace (prefixWord ++ tailWord_1573426) baseStart_1573426 baseEnd_1573426 := by
    simpa [prefixWord, tailWord_1573426, baseEnd_1573426] using wordTrace_append hprefix tailTrace_1573426
  have hstable : (prefixWord ++ tailWord_1573426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573426).length < 2 ^ (prefixWord ++ tailWord_1573426).sum := by decide
  have hdescent : baseEnd_1573426 < baseStart_1573426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573446 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1573446 : Nat := 118140960795 + 1573446 * 2 ^ 59
def prefixEnd_1573446 : Nat := 4983230072969 + 3 ^ 40 * 1573446 * 2
def baseEnd_1573446 : Nat := 359081814175269386217271

theorem tailTrace_1573446 : CollatzResearch.WordTrace tailWord_1573446 prefixEnd_1573446 359081814175269386217271 := by
  unfold tailWord_1573446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793384070552541875867631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38258860171787560018509461 1793384070552541875867631)
  ·
    refine ⟨2690076105828812813801447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1793384070552541875867631 2690076105828812813801447)
    ·
      refine ⟨4035114158743219220702171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690076105828812813801447 4035114158743219220702171)
      ·
        refine ⟨6052671238114828831053257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035114158743219220702171 6052671238114828831053257)
        ·
          refine ⟨4539503428586121623289943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6052671238114828831053257 4539503428586121623289943)
          ·
            refine ⟨6809255142879182434934915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539503428586121623289943 6809255142879182434934915)
            ·
              refine ⟨10213882714318773652402373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809255142879182434934915 10213882714318773652402373)
              ·
                refine ⟨1915103008934770059825445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10213882714318773652402373 1915103008934770059825445)
                ·
                  refine ⟨359081814175269386217271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915103008934770059825445 359081814175269386217271)
                  ·
                    rfl

theorem cell21_1573446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1573446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573446 prefixEnd_1573446 := by exact prefixLift 1573446
  have htrace : WordTrace (prefixWord ++ tailWord_1573446) baseStart_1573446 baseEnd_1573446 := by
    simpa [prefixWord, tailWord_1573446, baseEnd_1573446] using wordTrace_append hprefix tailTrace_1573446
  have hstable : (prefixWord ++ tailWord_1573446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573446).length < 2 ^ (prefixWord ++ tailWord_1573446).sum := by decide
  have hdescent : baseEnd_1573446 < baseStart_1573446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573522 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1573522 : Nat := 118140960795 + 1573522 * 2 ^ 59
def prefixEnd_1573522 : Nat := 4983230072969 + 3 ^ 40 * 1573522 * 2
def baseEnd_1573522 : Nat := 359099158410710142950449

theorem tailTrace_1573522 : CollatzResearch.WordTrace tailWord_1573522 prefixEnd_1573522 359099158410710142950449 := by
  unfold tailWord_1573522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347765551351501251882705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38260708136937336671687213 14347765551351501251882705)
  ·
    refine ⟨10760824163513625938912029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14347765551351501251882705 10760824163513625938912029)
    ·
      refine ⟨4035309061317609727092011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10760824163513625938912029 4035309061317609727092011)
      ·
        refine ⟨6052963591976414590638017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035309061317609727092011 6052963591976414590638017)
        ·
          refine ⟨4539722693982310942978513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6052963591976414590638017 4539722693982310942978513)
          ·
            refine ⟨3404792020486733207233885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539722693982310942978513 3404792020486733207233885)
            ·
              refine ⟨1276797007682524952712707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3404792020486733207233885 1276797007682524952712707)
              ·
                refine ⟨1915195511523787429069061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276797007682524952712707 1915195511523787429069061)
                ·
                  refine ⟨359099158410710142950449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915195511523787429069061 359099158410710142950449)
                  ·
                    rfl

theorem cell21_1573522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1573522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573522 prefixEnd_1573522 := by exact prefixLift 1573522
  have htrace : WordTrace (prefixWord ++ tailWord_1573522) baseStart_1573522 baseEnd_1573522 := by
    simpa [prefixWord, tailWord_1573522, baseEnd_1573522] using wordTrace_append hprefix tailTrace_1573522
  have hstable : (prefixWord ++ tailWord_1573522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573522).length < 2 ^ (prefixWord ++ tailWord_1573522).sum := by decide
  have hdescent : baseEnd_1573522 < baseStart_1573522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573533 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1573533 : Nat := 118140960795 + 1573533 * 2 ^ 59
def prefixEnd_1573533 : Nat := 4983230072969 + 3 ^ 40 * 1573533 * 2
def baseEnd_1573533 : Nat := 359101668760576568267093

theorem tailTrace_1573533 : CollatzResearch.WordTrace tailWord_1573533 prefixEnd_1573533 359101668760576568267093 := by
  unfold tailWord_1573533
  simp only [CollatzResearch.WordTrace]
  refine ⟨57391463408366153886181253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38260975605577435924120835 57391463408366153886181253)
  ·
    refine ⟨10760899389068653853658985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57391463408366153886181253 10760899389068653853658985)
    ·
      refine ⟨8070674541801490390244239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10760899389068653853658985 8070674541801490390244239)
      ·
        refine ⟨12106011812702235585366359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8070674541801490390244239 12106011812702235585366359)
        ·
          refine ⟨18159017719053353378049539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12106011812702235585366359 18159017719053353378049539)
          ·
            refine ⟨27238526578580030067074309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18159017719053353378049539 27238526578580030067074309)
            ·
              refine ⟨5107223733483755637576433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27238526578580030067074309 5107223733483755637576433)
              ·
                refine ⟨3830417800112816728182325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5107223733483755637576433 3830417800112816728182325)
                ·
                  refine ⟨359101668760576568267093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3830417800112816728182325 359101668760576568267093)
                  ·
                    rfl

theorem cell21_1573533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1573533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573533 prefixEnd_1573533 := by exact prefixLift 1573533
  have htrace : WordTrace (prefixWord ++ tailWord_1573533) baseStart_1573533 baseEnd_1573533 := by
    simpa [prefixWord, tailWord_1573533, baseEnd_1573533] using wordTrace_append hprefix tailTrace_1573533
  have hstable : (prefixWord ++ tailWord_1573533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573533).length < 2 ^ (prefixWord ++ tailWord_1573533).sum := by decide
  have hdescent : baseEnd_1573533 < baseStart_1573533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573536 : List Nat := [2, 1, 1, 4, 4, 2, 2, 5]
def baseStart_1573536 : Nat := 118140960795 + 1573536 * 2 ^ 59
def prefixEnd_1573536 : Nat := 4983230072969 + 3 ^ 40 * 1573536 * 2
def baseEnd_1573536 : Nat := 119700784467149743239029

theorem tailTrace_1573536 : CollatzResearch.WordTrace tailWord_1573536 prefixEnd_1573536 119700784467149743239029 := by
  unfold tailWord_1573536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28695786413677642699270231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38261048551570190265693641 28695786413677642699270231)
  ·
    refine ⟨43043679620516464048905347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28695786413677642699270231 43043679620516464048905347)
    ·
      refine ⟨64565519430774696073358021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43043679620516464048905347 64565519430774696073358021)
      ·
        refine ⟨12106034893270255513754629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64565519430774696073358021 12106034893270255513754629)
        ·
          refine ⟨2269881542488172908828993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12106034893270255513754629 2269881542488172908828993)
          ·
            refine ⟨1702411156866129681621745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269881542488172908828993 1702411156866129681621745)
            ·
              refine ⟨1276808367649597261216309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702411156866129681621745 1276808367649597261216309)
              ·
                refine ⟨119700784467149743239029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1276808367649597261216309 119700784467149743239029)
                ·
                  rfl

theorem cell21_1573536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 5].length) (baseStart_1573536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573536 prefixEnd_1573536 := by exact prefixLift 1573536
  have htrace : WordTrace (prefixWord ++ tailWord_1573536) baseStart_1573536 baseEnd_1573536 := by
    simpa [prefixWord, tailWord_1573536, baseEnd_1573536] using wordTrace_append hprefix tailTrace_1573536
  have hstable : (prefixWord ++ tailWord_1573536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573536).length < 2 ^ (prefixWord ++ tailWord_1573536).sum := by decide
  have hdescent : baseEnd_1573536 < baseStart_1573536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573564 : List Nat := [2, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1573564 : Nat := 118140960795 + 1573564 * 2 ^ 59
def prefixEnd_1573564 : Nat := 4983230072969 + 3 ^ 40 * 1573564 * 2
def baseEnd_1573564 : Nat := 359108743382927403250363

theorem tailTrace_1573564 : CollatzResearch.WordTrace tailWord_1573564 prefixEnd_1573564 359108743382927403250363 := by
  unfold tailWord_1573564
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696297035626923090279873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38261729380835897453706497 28696297035626923090279873)
  ·
    refine ⟨21522222776720192317709905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28696297035626923090279873 21522222776720192317709905)
    ·
      refine ⟨16141667082540144238282429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21522222776720192317709905 16141667082540144238282429)
      ·
        refine ⟨6053125155952554089355911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16141667082540144238282429 6053125155952554089355911)
        ·
          refine ⟨9079687733928831134033867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053125155952554089355911 9079687733928831134033867)
          ·
            refine ⟨13619531600893246701050801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079687733928831134033867 13619531600893246701050801)
            ·
              refine ⟨10214648700669935025788101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13619531600893246701050801 10214648700669935025788101)
              ·
                refine ⟨1915246631375612817335269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10214648700669935025788101 1915246631375612817335269)
                ·
                  refine ⟨359108743382927403250363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915246631375612817335269 359108743382927403250363)
                  ·
                    rfl

theorem cell21_1573564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1573564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573564 prefixEnd_1573564 := by exact prefixLift 1573564
  have htrace : WordTrace (prefixWord ++ tailWord_1573564) baseStart_1573564 baseEnd_1573564 := by
    simpa [prefixWord, tailWord_1573564, baseEnd_1573564] using wordTrace_append hprefix tailTrace_1573564
  have hstable : (prefixWord ++ tailWord_1573564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573564).length < 2 ^ (prefixWord ++ tailWord_1573564).sum := by decide
  have hdescent : baseEnd_1573564 < baseStart_1573564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573567 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 3]
def baseStart_1573567 : Nat := 118140960795 + 1573567 * 2 ^ 59
def prefixEnd_1573567 : Nat := 4983230072969 + 3 ^ 40 * 1573567 * 2
def baseEnd_1573567 : Nat := 359109428023800064700357

theorem tailTrace_1573567 : CollatzResearch.WordTrace tailWord_1573567 prefixEnd_1573567 359109428023800064700357 := by
  unfold tailWord_1573567
  simp only [CollatzResearch.WordTrace]
  refine ⟨57392703490242977692918955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38261802326828651795279303 57392703490242977692918955)
  ·
    refine ⟨86089055235364466539378433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57392703490242977692918955 86089055235364466539378433)
    ·
      refine ⟨64566791426523349904533825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86089055235364466539378433 64566791426523349904533825)
      ·
        refine ⟨48425093569892512428400369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64566791426523349904533825 48425093569892512428400369)
        ·
          refine ⟨36318820177419384321300277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48425093569892512428400369 36318820177419384321300277)
          ·
            refine ⟨3404889391633067280121901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36318820177419384321300277 3404889391633067280121901)
            ·
              refine ⟨1276833521862400230045713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3404889391633067280121901 1276833521862400230045713)
              ·
                refine ⟨957625141396800172534285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276833521862400230045713 957625141396800172534285)
                ·
                  refine ⟨359109428023800064700357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957625141396800172534285 359109428023800064700357)
                  ·
                    rfl

theorem cell21_1573567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].length) (baseStart_1573567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573567 prefixEnd_1573567 := by exact prefixLift 1573567
  have htrace : WordTrace (prefixWord ++ tailWord_1573567) baseStart_1573567 baseEnd_1573567 := by
    simpa [prefixWord, tailWord_1573567, baseEnd_1573567] using wordTrace_append hprefix tailTrace_1573567
  have hstable : (prefixWord ++ tailWord_1573567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573567).length < 2 ^ (prefixWord ++ tailWord_1573567).sum := by decide
  have hdescent : baseEnd_1573567 < baseStart_1573567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573578 : List Nat := [3, 1, 2, 1, 4, 1, 1, 8]
def baseStart_1573578 : Nat := 118140960795 + 1573578 * 2 ^ 59
def prefixEnd_1573578 : Nat := 4983230072969 + 3 ^ 40 * 1573578 * 2
def baseEnd_1573578 : Nat := 119703979457888830005667

theorem tailTrace_1573578 : CollatzResearch.WordTrace tailWord_1573578 prefixEnd_1573578 119703979457888830005667 := by
  unfold tailWord_1573578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348276173300781642892347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38262069795468751047712925 14348276173300781642892347)
  ·
    refine ⟨21522414259951172464338521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14348276173300781642892347 21522414259951172464338521)
    ·
      refine ⟨16141810694963379348253891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21522414259951172464338521 16141810694963379348253891)
      ·
        refine ⟨24212716042445069022380837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16141810694963379348253891 24212716042445069022380837)
        ·
          refine ⟨4539884257958450441696407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24212716042445069022380837 4539884257958450441696407)
          ·
            refine ⟨6809826386937675662544611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539884257958450441696407 6809826386937675662544611)
            ·
              refine ⟨10214739580406513493816917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809826386937675662544611 10214739580406513493816917)
              ·
                refine ⟨119703979457888830005667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10214739580406513493816917 119703979457888830005667)
                ·
                  rfl

theorem cell21_1573578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_1573578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573578 prefixEnd_1573578 := by exact prefixLift 1573578
  have htrace : WordTrace (prefixWord ++ tailWord_1573578) baseStart_1573578 baseEnd_1573578 := by
    simpa [prefixWord, tailWord_1573578, baseEnd_1573578] using wordTrace_append hprefix tailTrace_1573578
  have hstable : (prefixWord ++ tailWord_1573578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573578).length < 2 ^ (prefixWord ++ tailWord_1573578).sum := by decide
  have hdescent : baseEnd_1573578 < baseStart_1573578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573640 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_1573640 : Nat := 118140960795 + 1573640 * 2 ^ 59
def prefixEnd_1573640 : Nat := 4983230072969 + 3 ^ 40 * 1573640 * 2
def baseEnd_1573640 : Nat := 359126087618368159983541

theorem tailTrace_1573640 : CollatzResearch.WordTrace tailWord_1573640 prefixEnd_1573640 359126087618368159983541 := by
  unfold tailWord_1573640
  simp only [CollatzResearch.WordTrace]
  refine ⟨28697683009489255580163187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38263577345985674106884249 28697683009489255580163187)
  ·
    refine ⟨43046524514233883370244781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28697683009489255580163187 43046524514233883370244781)
    ·
      refine ⟨16142446692837706263841793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43046524514233883370244781 16142446692837706263841793)
      ·
        refine ⟨12106835019628279697881345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16142446692837706263841793 12106835019628279697881345)
        ·
          refine ⟨9080126264721209773411009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12106835019628279697881345 9080126264721209773411009)
          ·
            refine ⟨6810094698540907330058257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080126264721209773411009 6810094698540907330058257)
            ·
              refine ⟨5107571023905680497543693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6810094698540907330058257 5107571023905680497543693)
              ·
                refine ⟨1915339133964630186578885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5107571023905680497543693 1915339133964630186578885)
                ·
                  refine ⟨359126087618368159983541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915339133964630186578885 359126087618368159983541)
                  ·
                    rfl

theorem cell21_1573640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_1573640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573640 prefixEnd_1573640 := by exact prefixLift 1573640
  have htrace : WordTrace (prefixWord ++ tailWord_1573640) baseStart_1573640 baseEnd_1573640 := by
    simpa [prefixWord, tailWord_1573640, baseEnd_1573640] using wordTrace_append hprefix tailTrace_1573640
  have hstable : (prefixWord ++ tailWord_1573640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573640).length < 2 ^ (prefixWord ++ tailWord_1573640).sum := by decide
  have hdescent : baseEnd_1573640 < baseStart_1573640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573685 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_1573685 : Nat := 118140960795 + 1573685 * 2 ^ 59
def prefixEnd_1573685 : Nat := 4983230072969 + 3 ^ 40 * 1573685 * 2
def baseEnd_1573685 : Nat := 359136357231458081733449

theorem tailTrace_1573685 : CollatzResearch.WordTrace tailWord_1573685 prefixEnd_1573685 359136357231458081733449 := by
  unfold tailWord_1573685
  simp only [CollatzResearch.WordTrace]
  refine ⟨57397007303815483845714509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38264671535876989230476339 57397007303815483845714509)
  ·
    refine ⟨21523877738930806442142941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57397007303815483845714509 21523877738930806442142941)
    ·
      refine ⟨8071454152099052415803603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21523877738930806442142941 8071454152099052415803603)
      ·
        refine ⟨12107181228148578623705405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8071454152099052415803603 12107181228148578623705405)
        ·
          refine ⟨4540192960555716983889527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12107181228148578623705405 4540192960555716983889527)
          ·
            refine ⟨6810289440833575475834291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540192960555716983889527 6810289440833575475834291)
            ·
              refine ⟨10215434161250363213751437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810289440833575475834291 10215434161250363213751437)
              ·
                refine ⟨3830787810468886205156789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10215434161250363213751437 3830787810468886205156789)
                ·
                  refine ⟨359136357231458081733449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3830787810468886205156789 359136357231458081733449)
                  ·
                    rfl

theorem cell21_1573685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_1573685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573685 prefixEnd_1573685 := by exact prefixLift 1573685
  have htrace : WordTrace (prefixWord ++ tailWord_1573685) baseStart_1573685 baseEnd_1573685 := by
    simpa [prefixWord, tailWord_1573685, baseEnd_1573685] using wordTrace_append hprefix tailTrace_1573685
  have hstable : (prefixWord ++ tailWord_1573685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573685).length < 2 ^ (prefixWord ++ tailWord_1573685).sum := by decide
  have hdescent : baseEnd_1573685 < baseStart_1573685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573719 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 3]
def baseStart_1573719 : Nat := 118140960795 + 1573719 * 2 ^ 59
def prefixEnd_1573719 : Nat := 4983230072969 + 3 ^ 40 * 1573719 * 2
def baseEnd_1573719 : Nat := 359144116494681578166713

theorem tailTrace_1573719 : CollatzResearch.WordTrace tailWord_1573719 prefixEnd_1573719 359144116494681578166713 := by
  unfold tailWord_1573719
  simp only [CollatzResearch.WordTrace]
  refine ⟨57398247385692307652452211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38265498257128205101634807 57398247385692307652452211)
  ·
    refine ⟨86097371078538461478678317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57398247385692307652452211 86097371078538461478678317)
    ·
      refine ⟨32286514154451923054504369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86097371078538461478678317 32286514154451923054504369)
      ·
        refine ⟨24214885615838942290878277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32286514154451923054504369 24214885615838942290878277)
        ·
          refine ⟨4540291052969801679539677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24214885615838942290878277 4540291052969801679539677)
          ·
            refine ⟨1702609144863675629827379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4540291052969801679539677 1702609144863675629827379)
            ·
              refine ⟨2553913717295513444741069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702609144863675629827379 2553913717295513444741069)
              ·
                refine ⟨957717643985817541777901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2553913717295513444741069 957717643985817541777901)
                ·
                  refine ⟨359144116494681578166713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957717643985817541777901 359144116494681578166713)
                  ·
                    rfl

theorem cell21_1573719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].length) (baseStart_1573719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573719 prefixEnd_1573719 := by exact prefixLift 1573719
  have htrace : WordTrace (prefixWord ++ tailWord_1573719) baseStart_1573719 baseEnd_1573719 := by
    simpa [prefixWord, tailWord_1573719, baseEnd_1573719] using wordTrace_append hprefix tailTrace_1573719
  have hstable : (prefixWord ++ tailWord_1573719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573719).length < 2 ^ (prefixWord ++ tailWord_1573719).sum := by decide
  have hdescent : baseEnd_1573719 < baseStart_1573719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573750 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1573750 : Nat := 118140960795 + 1573750 * 2 ^ 59
def prefixEnd_1573750 : Nat := 4983230072969 + 3 ^ 40 * 1573750 * 2
def baseEnd_1573750 : Nat := 359151191117032413149983

theorem tailTrace_1573750 : CollatzResearch.WordTrace tailWord_1573750 prefixEnd_1573750 359151191117032413149983 := by
  unfold tailWord_1573750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587461128036249996676919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38266252032386666631220469 3587461128036249996676919)
  ·
    refine ⟨5381191692054374995015379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3587461128036249996676919 5381191692054374995015379)
    ·
      refine ⟨8071787538081562492523069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5381191692054374995015379 8071787538081562492523069)
      ·
        refine ⟨3026920326780585934696151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8071787538081562492523069 3026920326780585934696151)
        ·
          refine ⟨4540380490170878902044227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026920326780585934696151 4540380490170878902044227)
          ·
            refine ⟨6810570735256318353066341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4540380490170878902044227 6810570735256318353066341)
            ·
              refine ⟨1276982012860559691199939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6810570735256318353066341 1276982012860559691199939)
              ·
                refine ⟨1915473019290839536799909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276982012860559691199939 1915473019290839536799909)
                ·
                  refine ⟨359151191117032413149983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915473019290839536799909 359151191117032413149983)
                  ·
                    rfl

theorem cell21_1573750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1573750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573750 prefixEnd_1573750 := by exact prefixLift 1573750
  have htrace : WordTrace (prefixWord ++ tailWord_1573750) baseStart_1573750 baseEnd_1573750 := by
    simpa [prefixWord, tailWord_1573750, baseEnd_1573750] using wordTrace_append hprefix tailTrace_1573750
  have hstable : (prefixWord ++ tailWord_1573750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573750).length < 2 ^ (prefixWord ++ tailWord_1573750).sum := by decide
  have hdescent : baseEnd_1573750 < baseStart_1573750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573913 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 3]
def baseStart_1573913 : Nat := 118140960795 + 1573913 * 2 ^ 59
def prefixEnd_1573913 : Nat := 4983230072969 + 3 ^ 40 * 1573913 * 2
def baseEnd_1573913 : Nat := 359188389937780351932983

theorem tailTrace_1573913 : CollatzResearch.WordTrace tailWord_1573913 prefixEnd_1573913 359188389937780351932983 := by
  unfold tailWord_1573913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57405323146989478785014393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38270215431326319190009595 57405323146989478785014393)
  ·
    refine ⟨43053992360242109088760795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57405323146989478785014393 43053992360242109088760795)
    ·
      refine ⟨64580988540363163633141193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43053992360242109088760795 64580988540363163633141193)
      ·
        refine ⟨48435741405272372724855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64580988540363163633141193 48435741405272372724855895)
        ·
          refine ⟨72653612107908559087283843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48435741405272372724855895 72653612107908559087283843)
          ·
            refine ⟨108980418161862838630925765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72653612107908559087283843 108980418161862838630925765)
            ·
              refine ⟨20433828405349282243298581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108980418161862838630925765 20433828405349282243298581)
              ·
                refine ⟨957835706500747605154621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20433828405349282243298581 957835706500747605154621)
                ·
                  refine ⟨359188389937780351932983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 957835706500747605154621 359188389937780351932983)
                  ·
                    rfl

theorem cell21_1573913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_1573913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573913 prefixEnd_1573913 := by exact prefixLift 1573913
  have htrace : WordTrace (prefixWord ++ tailWord_1573913) baseStart_1573913 baseEnd_1573913 := by
    simpa [prefixWord, tailWord_1573913, baseEnd_1573913] using wordTrace_append hprefix tailTrace_1573913
  have hstable : (prefixWord ++ tailWord_1573913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573913).length < 2 ^ (prefixWord ++ tailWord_1573913).sum := by decide
  have hdescent : baseEnd_1573913 < baseStart_1573913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573992 : List Nat := [2, 1, 4, 4, 1, 1, 3, 5]
def baseStart_1573992 : Nat := 118140960795 + 1573992 * 2 ^ 59
def prefixEnd_1573992 : Nat := 4983230072969 + 3 ^ 40 * 1573992 * 2
def baseEnd_1573992 : Nat := 119735472938031256705385

theorem tailTrace_1573992 : CollatzResearch.WordTrace tailWord_1573992 prefixEnd_1573992 119735472938031256705385 := by
  unfold tailWord_1573992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704102256851637638570115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38272136342468850184760153 28704102256851637638570115)
  ·
    refine ⟨43056153385277456457855173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28704102256851637638570115 43056153385277456457855173)
    ·
      refine ⟨8073028759739523085847845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43056153385277456457855173 8073028759739523085847845)
      ·
        refine ⟨1513692892451160578596471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8073028759739523085847845 1513692892451160578596471)
        ·
          refine ⟨2270539338676740867894707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513692892451160578596471 2270539338676740867894707)
          ·
            refine ⟨3405809008015111301842061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2270539338676740867894707 3405809008015111301842061)
            ·
              refine ⟨1277178378005666738190773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3405809008015111301842061 1277178378005666738190773)
              ·
                refine ⟨119735472938031256705385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1277178378005666738190773 119735472938031256705385)
                ·
                  rfl

theorem cell21_1573992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_1573992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1573992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1573992 prefixEnd_1573992 := by exact prefixLift 1573992
  have htrace : WordTrace (prefixWord ++ tailWord_1573992) baseStart_1573992 baseEnd_1573992 := by
    simpa [prefixWord, tailWord_1573992, baseEnd_1573992] using wordTrace_append hprefix tailTrace_1573992
  have hstable : (prefixWord ++ tailWord_1573992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573992).length < 2 ^ (prefixWord ++ tailWord_1573992).sum := by decide
  have hdescent : baseEnd_1573992 < baseStart_1573992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574020 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_1574020 : Nat := 118140960795 + 1574020 * 2 ^ 59
def prefixEnd_1574020 : Nat := 4983230072969 + 3 ^ 40 * 1574020 * 2
def baseEnd_1574020 : Nat := 359212808795571943649431

theorem tailTrace_1574020 : CollatzResearch.WordTrace tailWord_1574020 prefixEnd_1574020 359212808795571943649431 := by
  unfold tailWord_1574020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704612878800918029579757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38272817171734557372773009 28704612878800918029579757)
  ·
    refine ⟨10764229829550344261092409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28704612878800918029579757 10764229829550344261092409)
    ·
      refine ⟨8073172372162758195819307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10764229829550344261092409 8073172372162758195819307)
      ·
        refine ⟨12109758558244137293728961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8073172372162758195819307 12109758558244137293728961)
        ·
          refine ⟨9082318918683102970296721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12109758558244137293728961 9082318918683102970296721)
          ·
            refine ⟨6811739189012327227722541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9082318918683102970296721 6811739189012327227722541)
            ·
              refine ⟨2554402195879622710395953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6811739189012327227722541 2554402195879622710395953)
              ·
                refine ⟨1915801646909717032796965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554402195879622710395953 1915801646909717032796965)
                ·
                  refine ⟨359212808795571943649431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915801646909717032796965 359212808795571943649431)
                  ·
                    rfl

theorem cell21_1574020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_1574020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574020 prefixEnd_1574020 := by exact prefixLift 1574020
  have htrace : WordTrace (prefixWord ++ tailWord_1574020) baseStart_1574020 baseEnd_1574020 := by
    simpa [prefixWord, tailWord_1574020, baseEnd_1574020] using wordTrace_append hprefix tailTrace_1574020
  have hstable : (prefixWord ++ tailWord_1574020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574020).length < 2 ^ (prefixWord ++ tailWord_1574020).sum := by decide
  have hdescent : baseEnd_1574020 < baseStart_1574020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574048 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 5]
def baseStart_1574048 : Nat := 118140960795 + 1574048 * 2 ^ 59
def prefixEnd_1574048 : Nat := 4983230072969 + 3 ^ 40 * 1574048 * 2
def baseEnd_1574048 : Nat := 359219198777050117182707

theorem tailTrace_1574048 : CollatzResearch.WordTrace tailWord_1574048 prefixEnd_1574048 359219198777050117182707 := by
  unfold tailWord_1574048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28705123500750198420589399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38273498001000264560785865 28705123500750198420589399)
  ·
    refine ⟨43057685251125297630884099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28705123500750198420589399 43057685251125297630884099)
    ·
      refine ⟨64586527876687946446326149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43057685251125297630884099 64586527876687946446326149)
      ·
        refine ⟨12109973976878989958686153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64586527876687946446326149 12109973976878989958686153)
        ·
          refine ⟨9082480482659242469014615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12109973976878989958686153 9082480482659242469014615)
          ·
            refine ⟨13623720723988863703521923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9082480482659242469014615 13623720723988863703521923)
            ·
              refine ⟨20435581085983295555282885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13623720723988863703521923 20435581085983295555282885)
              ·
                refine ⟨3831671453621867916615541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20435581085983295555282885 3831671453621867916615541)
                ·
                  refine ⟨359219198777050117182707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3831671453621867916615541 359219198777050117182707)
                  ·
                    rfl

theorem cell21_1574048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_1574048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574048 prefixEnd_1574048 := by exact prefixLift 1574048
  have htrace : WordTrace (prefixWord ++ tailWord_1574048) baseStart_1574048 baseEnd_1574048 := by
    simpa [prefixWord, tailWord_1574048, baseEnd_1574048] using wordTrace_append hprefix tailTrace_1574048
  have hstable : (prefixWord ++ tailWord_1574048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574048).length < 2 ^ (prefixWord ++ tailWord_1574048).sum := by decide
  have hdescent : baseEnd_1574048 < baseStart_1574048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574155 : List Nat := [1, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_1574155 : Nat := 118140960795 + 1574155 * 2 ^ 59
def prefixEnd_1574155 : Nat := 4983230072969 + 3 ^ 40 * 1574155 * 2
def baseEnd_1574155 : Nat := 359243617634841708899155

theorem tailTrace_1574155 : CollatzResearch.WordTrace tailWord_1574155 prefixEnd_1574155 359243617634841708899155 := by
  unfold tailWord_1574155
  simp only [CollatzResearch.WordTrace]
  refine ⟨57414149612112754115323919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276099741408502743549279 57414149612112754115323919)
  ·
    refine ⟨86121224418169131172985879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57414149612112754115323919 86121224418169131172985879)
    ·
      refine ⟨129181836627253696759478819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86121224418169131172985879 129181836627253696759478819)
      ·
        refine ⟨193772754940880545139218229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129181836627253696759478819 193772754940880545139218229)
        ·
          refine ⟨18166195775707551106801709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193772754940880545139218229 18166195775707551106801709)
          ·
            refine ⟨6812323415890331665050641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18166195775707551106801709 6812323415890331665050641)
            ·
              refine ⟨5109242561917748748787981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6812323415890331665050641 5109242561917748748787981)
              ·
                refine ⟨1915965960719155780795493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5109242561917748748787981 1915965960719155780795493)
                ·
                  refine ⟨359243617634841708899155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1915965960719155780795493 359243617634841708899155)
                  ·
                    rfl

theorem cell21_1574155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_1574155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574155 prefixEnd_1574155 := by exact prefixLift 1574155
  have htrace : WordTrace (prefixWord ++ tailWord_1574155) baseStart_1574155 baseEnd_1574155 := by
    simpa [prefixWord, tailWord_1574155, baseEnd_1574155] using wordTrace_append hprefix tailTrace_1574155
  have hstable : (prefixWord ++ tailWord_1574155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574155).length < 2 ^ (prefixWord ++ tailWord_1574155).sum := by decide
  have hdescent : baseEnd_1574155 < baseStart_1574155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574186 : List Nat := [3, 1, 4, 2, 1, 2, 8]
def baseStart_1574186 : Nat := 118140960795 + 1574186 * 2 ^ 59
def prefixEnd_1574186 : Nat := 4983230072969 + 3 ^ 40 * 1574186 * 2
def baseEnd_1574186 : Nat := 39916743584132504875825

theorem tailTrace_1574186 : CollatzResearch.WordTrace tailWord_1574186 prefixEnd_1574186 39916743584132504875825 := by
  unfold tailWord_1574186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353820068750111602425603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38276853516666964273134941 14353820068750111602425603)
  ·
    refine ⟨21530730103125167403638405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14353820068750111602425603 21530730103125167403638405)
    ·
      refine ⟨4037011894335968888182201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21530730103125167403638405 4037011894335968888182201)
      ·
        refine ⟨3027758920751976666136651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4037011894335968888182201 3027758920751976666136651)
        ·
          refine ⟨4541638381127964999204977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027758920751976666136651 4541638381127964999204977)
          ·
            refine ⟨3406228785845973749403733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4541638381127964999204977 3406228785845973749403733)
            ·
              refine ⟨39916743584132504875825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3406228785845973749403733 39916743584132504875825)
              ·
                rfl

theorem cell21_1574186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 8].length) (baseStart_1574186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574186 prefixEnd_1574186 := by exact prefixLift 1574186
  have htrace : WordTrace (prefixWord ++ tailWord_1574186) baseStart_1574186 baseEnd_1574186 := by
    simpa [prefixWord, tailWord_1574186, baseEnd_1574186] using wordTrace_append hprefix tailTrace_1574186
  have hstable : (prefixWord ++ tailWord_1574186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574186).length < 2 ^ (prefixWord ++ tailWord_1574186).sum := by decide
  have hdescent : baseEnd_1574186 < baseStart_1574186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574189 : List Nat := [1, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1574189 : Nat := 118140960795 + 1574189 * 2 ^ 59
def prefixEnd_1574189 : Nat := 4983230072969 + 3 ^ 40 * 1574189 * 2
def baseEnd_1574189 : Nat := 359251376898065205332419

theorem tailTrace_1574189 : CollatzResearch.WordTrace tailWord_1574189 prefixEnd_1574189 359251376898065205332419 := by
  unfold tailWord_1574189
  simp only [CollatzResearch.WordTrace]
  refine ⟨57415389693989577922061621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38276926462659718614707747 57415389693989577922061621)
  ·
    refine ⟨5382692783811522930193277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57415389693989577922061621 5382692783811522930193277)
    ·
      refine ⟨2018509793929321098822479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5382692783811522930193277 2018509793929321098822479)
      ·
        refine ⟨3027764690893981648233719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018509793929321098822479 3027764690893981648233719)
        ·
          refine ⟨4541647036340972472350579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027764690893981648233719 4541647036340972472350579)
          ·
            refine ⟨6812470554511458708525869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4541647036340972472350579 6812470554511458708525869)
            ·
              refine ⟨2554676457941797015697201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6812470554511458708525869 2554676457941797015697201)
              ·
                refine ⟨1916007343456347761772901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554676457941797015697201 1916007343456347761772901)
                ·
                  refine ⟨359251376898065205332419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916007343456347761772901 359251376898065205332419)
                  ·
                    rfl

theorem cell21_1574189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1574189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574189 prefixEnd_1574189 := by exact prefixLift 1574189
  have htrace : WordTrace (prefixWord ++ tailWord_1574189) baseStart_1574189 baseEnd_1574189 := by
    simpa [prefixWord, tailWord_1574189, baseEnd_1574189] using wordTrace_append hprefix tailTrace_1574189
  have hstable : (prefixWord ++ tailWord_1574189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574189).length < 2 ^ (prefixWord ++ tailWord_1574189).sum := by decide
  have hdescent : baseEnd_1574189 < baseStart_1574189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574237 : List Nat := [1, 4, 5, 1, 2, 1, 7]
def baseStart_1574237 : Nat := 118140960795 + 1574237 * 2 ^ 59
def prefixEnd_1574237 : Nat := 4983230072969 + 3 ^ 40 * 1574237 * 2
def baseEnd_1574237 : Nat := 39918036794669754281369

theorem tailTrace_1574237 : CollatzResearch.WordTrace tailWord_1574237 prefixEnd_1574237 39918036794669754281369 := by
  unfold tailWord_1574237
  simp only [CollatzResearch.WordTrace]
  refine ⟨57417140397815682119808965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38278093598543788079872643 57417140397815682119808965)
  ·
    refine ⟨10765713824590440397464181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57417140397815682119808965 10765713824590440397464181)
    ·
      refine ⟨1009285671055353787262267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10765713824590440397464181 1009285671055353787262267)
      ·
        refine ⟨1513928506583030680893401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009285671055353787262267 1513928506583030680893401)
        ·
          refine ⟨1135446379937273010670051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513928506583030680893401 1135446379937273010670051)
          ·
            refine ⟨1703169569905909516005077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135446379937273010670051 1703169569905909516005077)
            ·
              refine ⟨39918036794669754281369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1703169569905909516005077 39918036794669754281369)
              ·
                rfl

theorem cell21_1574237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 7].length) (baseStart_1574237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574237 prefixEnd_1574237 := by exact prefixLift 1574237
  have htrace : WordTrace (prefixWord ++ tailWord_1574237) baseStart_1574237 baseEnd_1574237 := by
    simpa [prefixWord, tailWord_1574237, baseEnd_1574237] using wordTrace_append hprefix tailTrace_1574237
  have hstable : (prefixWord ++ tailWord_1574237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574237).length < 2 ^ (prefixWord ++ tailWord_1574237).sum := by decide
  have hdescent : baseEnd_1574237 < baseStart_1574237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574307 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_1574307 : Nat := 118140960795 + 1574307 * 2 ^ 59
def prefixEnd_1574307 : Nat := 4983230072969 + 3 ^ 40 * 1574307 * 2
def baseEnd_1574307 : Nat := 359278306105723222365511

theorem tailTrace_1574307 : CollatzResearch.WordTrace tailWord_1574307 prefixEnd_1574307 359278306105723222365511 := by
  unfold tailWord_1574307
  simp only [CollatzResearch.WordTrace]
  refine ⟨57419693507562084074857175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38279795671708056049904783 57419693507562084074857175)
  ·
    refine ⟨86129540261343126112285763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57419693507562084074857175 86129540261343126112285763)
    ·
      refine ⟨129194310392014689168428645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86129540261343126112285763 129194310392014689168428645)
      ·
        refine ⟨24223933198502754219080371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129194310392014689168428645 24223933198502754219080371)
        ·
          refine ⟨36335899797754131328620557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223933198502754219080371 36335899797754131328620557)
          ·
            refine ⟨13625962424157799248232709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36335899797754131328620557 13625962424157799248232709)
            ·
              refine ⟨2554867954529587359043633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13625962424157799248232709 2554867954529587359043633)
              ·
                refine ⟨1916150965897190519282725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2554867954529587359043633 1916150965897190519282725)
                ·
                  refine ⟨359278306105723222365511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916150965897190519282725 359278306105723222365511)
                  ·
                    rfl

theorem cell21_1574307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_1574307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574307 prefixEnd_1574307 := by exact prefixLift 1574307
  have htrace : WordTrace (prefixWord ++ tailWord_1574307) baseStart_1574307 baseEnd_1574307 := by
    simpa [prefixWord, tailWord_1574307, baseEnd_1574307] using wordTrace_append hprefix tailTrace_1574307
  have hstable : (prefixWord ++ tailWord_1574307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574307).length < 2 ^ (prefixWord ++ tailWord_1574307).sum := by decide
  have hdescent : baseEnd_1574307 < baseStart_1574307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574369 : List Nat := [1, 2, 3, 1, 2, 3, 2, 4, 3]
def baseStart_1574369 : Nat := 118140960795 + 1574369 * 2 ^ 59
def prefixEnd_1574369 : Nat := 4983230072969 + 3 ^ 40 * 1574369 * 2
def baseEnd_1574369 : Nat := 359292455350424892332051

theorem tailTrace_1574369 : CollatzResearch.WordTrace tailWord_1574369 prefixEnd_1574369 359292455350424892332051 := by
  unfold tailWord_1574369
  simp only [CollatzResearch.WordTrace]
  refine ⟨57421954833337468663614161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38281303222224979109076107 57421954833337468663614161)
  ·
    refine ⟨43066466125003101497710621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57421954833337468663614161 43066466125003101497710621)
    ·
      refine ⟨16149924796876163061641483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43066466125003101497710621 16149924796876163061641483)
      ·
        refine ⟨24224887195314244592462225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16149924796876163061641483 24224887195314244592462225)
        ·
          refine ⟨18168665396485683444346669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24224887195314244592462225 18168665396485683444346669)
          ·
            refine ⟨6813249523682131291630001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18168665396485683444346669 6813249523682131291630001)
            ·
              refine ⟨5109937142761598468722501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6813249523682131291630001 5109937142761598468722501)
              ·
                refine ⟨958113214267799712885469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5109937142761598468722501 958113214267799712885469)
                ·
                  refine ⟨359292455350424892332051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958113214267799712885469 359292455350424892332051)
                  ·
                    rfl

theorem cell21_1574369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_1574369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574369 prefixEnd_1574369 := by exact prefixLift 1574369
  have htrace : WordTrace (prefixWord ++ tailWord_1574369) baseStart_1574369 baseEnd_1574369 := by
    simpa [prefixWord, tailWord_1574369, baseEnd_1574369] using wordTrace_append hprefix tailTrace_1574369
  have hstable : (prefixWord ++ tailWord_1574369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574369).length < 2 ^ (prefixWord ++ tailWord_1574369).sum := by decide
  have hdescent : baseEnd_1574369 < baseStart_1574369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574397 : List Nat := [1, 4, 1, 1, 1, 5, 1, 7]
def baseStart_1574397 : Nat := 118140960795 + 1574397 * 2 ^ 59
def prefixEnd_1574397 : Nat := 4983230072969 + 3 ^ 40 * 1574397 * 2
def baseEnd_1574397 : Nat := 119766281777301021955109

theorem tailTrace_1574397 : CollatzResearch.WordTrace tailWord_1574397 prefixEnd_1574397 119766281777301021955109 := by
  unfold tailWord_1574397
  simp only [CollatzResearch.WordTrace]
  refine ⟨57422976077236029445633445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38281984051490686297088963 57422976077236029445633445)
  ·
    refine ⟨10766808014481755521056271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57422976077236029445633445 10766808014481755521056271)
    ·
      refine ⟨16150212021722633281584407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766808014481755521056271 16150212021722633281584407)
      ·
        refine ⟨24225318032583949922376611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16150212021722633281584407 24225318032583949922376611)
        ·
          refine ⟨36337977048875924883564917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24225318032583949922376611 36337977048875924883564917)
          ·
            refine ⟨3406685348332117957834211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36337977048875924883564917 3406685348332117957834211)
            ·
              refine ⟨5110028022498176936751317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3406685348332117957834211 5110028022498176936751317)
              ·
                refine ⟨119766281777301021955109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5110028022498176936751317 119766281777301021955109)
                ·
                  rfl

theorem cell21_1574397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_1574397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574397 prefixEnd_1574397 := by exact prefixLift 1574397
  have htrace : WordTrace (prefixWord ++ tailWord_1574397) baseStart_1574397 baseEnd_1574397 := by
    simpa [prefixWord, tailWord_1574397, baseEnd_1574397] using wordTrace_append hprefix tailTrace_1574397
  have hstable : (prefixWord ++ tailWord_1574397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574397).length < 2 ^ (prefixWord ++ tailWord_1574397).sum := by decide
  have hdescent : baseEnd_1574397 < baseStart_1574397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574414 : List Nat := [4, 1, 1, 2, 4, 2, 7]
def baseStart_1574414 : Nat := 118140960795 + 1574414 * 2 ^ 59
def prefixEnd_1574414 : Nat := 4983230072969 + 3 ^ 40 * 1574414 * 2
def baseEnd_1574414 : Nat := 39922524995946090453551

theorem tailTrace_1574414 : CollatzResearch.WordTrace tailWord_1574414 prefixEnd_1574414 39922524995946090453551 := by
  unfold tailWord_1574414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177949514771805168625287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38282397412116294232668197 7177949514771805168625287)
  ·
    refine ⟨10766924272157707752937931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177949514771805168625287 10766924272157707752937931)
    ·
      refine ⟨16150386408236561629406897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766924272157707752937931 16150386408236561629406897)
      ·
        refine ⟨12112789806177421222055173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16150386408236561629406897 12112789806177421222055173)
        ·
          refine ⟨2271148088658266479135345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12112789806177421222055173 2271148088658266479135345)
          ·
            refine ⟨1703361066493699859351509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271148088658266479135345 1703361066493699859351509)
            ·
              refine ⟨39922524995946090453551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1703361066493699859351509 39922524995946090453551)
              ·
                rfl

theorem cell21_1574414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 7].length) (baseStart_1574414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574414 prefixEnd_1574414 := by exact prefixLift 1574414
  have htrace : WordTrace (prefixWord ++ tailWord_1574414) baseStart_1574414 baseEnd_1574414 := by
    simpa [prefixWord, tailWord_1574414, baseEnd_1574414] using wordTrace_append hprefix tailTrace_1574414
  have hstable : (prefixWord ++ tailWord_1574414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574414).length < 2 ^ (prefixWord ++ tailWord_1574414).sum := by decide
  have hdescent : baseEnd_1574414 < baseStart_1574414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574420 : List Nat := [2, 4, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1574420 : Nat := 118140960795 + 1574420 * 2 ^ 59
def prefixEnd_1574420 : Nat := 4983230072969 + 3 ^ 40 * 1574420 * 2
def baseEnd_1574420 : Nat := 359304094245260136981947

theorem tailTrace_1574420 : CollatzResearch.WordTrace tailWord_1574420 prefixEnd_1574420 359304094245260136981947 := by
  unfold tailWord_1574420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28711907478076352186860357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38282543304101802915813809 28711907478076352186860357)
  ·
    refine ⟨5383482652139316035036317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28711907478076352186860357 5383482652139316035036317)
    ·
      refine ⟨2018805994552243513138619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5383482652139316035036317 2018805994552243513138619)
      ·
        refine ⟨3028208991828365269707929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018805994552243513138619 3028208991828365269707929)
        ·
          refine ⟨2271156743871273952280947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028208991828365269707929 2271156743871273952280947)
          ·
            refine ⟨3406735115806910928421421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271156743871273952280947 3406735115806910928421421)
            ·
              refine ⟨1277525668427591598158033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3406735115806910928421421 1277525668427591598158033)
              ·
                refine ⟨958144251320693698618525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277525668427591598158033 958144251320693698618525)
                ·
                  refine ⟨359304094245260136981947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958144251320693698618525 359304094245260136981947)
                  ·
                    rfl

theorem cell21_1574420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1574420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574420 prefixEnd_1574420 := by exact prefixLift 1574420
  have htrace : WordTrace (prefixWord ++ tailWord_1574420) baseStart_1574420 baseEnd_1574420 := by
    simpa [prefixWord, tailWord_1574420, baseEnd_1574420] using wordTrace_append hprefix tailTrace_1574420
  have hstable : (prefixWord ++ tailWord_1574420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574420).length < 2 ^ (prefixWord ++ tailWord_1574420).sum := by decide
  have hdescent : baseEnd_1574420 < baseStart_1574420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574504 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_1574504 : Nat := 118140960795 + 1574504 * 2 ^ 59
def prefixEnd_1574504 : Nat := 4983230072969 + 3 ^ 40 * 1574504 * 2
def baseEnd_1574504 : Nat := 359323264189694657581775

theorem tailTrace_1574504 : CollatzResearch.WordTrace tailWord_1574504 prefixEnd_1574504 359323264189694657581775 := by
  unfold tailWord_1574504
  simp only [CollatzResearch.WordTrace]
  refine ⟨28713439343924193359889283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38284585791898924479852377 28713439343924193359889283)
  ·
    refine ⟨43070159015886290039833925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28713439343924193359889283 43070159015886290039833925)
    ·
      refine ⟨8075654815478679382468861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43070159015886290039833925 8075654815478679382468861)
      ·
        refine ⟨3028370555804504768425823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8075654815478679382468861 3028370555804504768425823)
        ·
          refine ⟨4542555833706757152638735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028370555804504768425823 4542555833706757152638735)
          ·
            refine ⟨6813833750560135728958103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4542555833706757152638735 6813833750560135728958103)
            ·
              refine ⟨10220750625840203593437155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6813833750560135728958103 10220750625840203593437155)
              ·
                refine ⟨15331125938760305390155733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10220750625840203593437155 15331125938760305390155733)
                ·
                  refine ⟨359323264189694657581775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15331125938760305390155733 359323264189694657581775)
                  ·
                    rfl

theorem cell21_1574504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_1574504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574504 prefixEnd_1574504 := by exact prefixLift 1574504
  have htrace : WordTrace (prefixWord ++ tailWord_1574504) baseStart_1574504 baseEnd_1574504 := by
    simpa [prefixWord, tailWord_1574504, baseEnd_1574504] using wordTrace_append hprefix tailTrace_1574504
  have hstable : (prefixWord ++ tailWord_1574504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574504).length < 2 ^ (prefixWord ++ tailWord_1574504).sum := by decide
  have hdescent : baseEnd_1574504 < baseStart_1574504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574521 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 3]
def baseStart_1574521 : Nat := 118140960795 + 1574521 * 2 ^ 59
def prefixEnd_1574521 : Nat := 4983230072969 + 3 ^ 40 * 1574521 * 2
def baseEnd_1574521 : Nat := 359327143821306405798407

theorem tailTrace_1574521 : CollatzResearch.WordTrace tailWord_1574521 prefixEnd_1574521 359327143821306405798407 := by
  unfold tailWord_1574521
  simp only [CollatzResearch.WordTrace]
  refine ⟨57427498728786798623147417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38284999152524532415431611 57427498728786798623147417)
  ·
    refine ⟨43070624046590098967360563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57427498728786798623147417 43070624046590098967360563)
    ·
      refine ⟨64605936069885148451040845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43070624046590098967360563 64605936069885148451040845)
      ·
        refine ⟨24227226026206930669140317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64605936069885148451040845 24227226026206930669140317)
        ·
          refine ⟨9085209759827599000927619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24227226026206930669140317 9085209759827599000927619)
          ·
            refine ⟨13627814639741398501391429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9085209759827599000927619 13627814639741398501391429)
            ·
              refine ⟨2555215244951512219010893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13627814639741398501391429 2555215244951512219010893)
              ·
                refine ⟨958205716856817082129085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555215244951512219010893 958205716856817082129085)
                ·
                  refine ⟨359327143821306405798407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958205716856817082129085 359327143821306405798407)
                  ·
                    rfl

theorem cell21_1574521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_1574521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574521 prefixEnd_1574521 := by exact prefixLift 1574521
  have htrace : WordTrace (prefixWord ++ tailWord_1574521) baseStart_1574521 baseEnd_1574521 := by
    simpa [prefixWord, tailWord_1574521, baseEnd_1574521] using wordTrace_append hprefix tailTrace_1574521
  have hstable : (prefixWord ++ tailWord_1574521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574521).length < 2 ^ (prefixWord ++ tailWord_1574521).sum := by decide
  have hdescent : baseEnd_1574521 < baseStart_1574521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574535 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_1574535 : Nat := 118140960795 + 1574535 * 2 ^ 59
def prefixEnd_1574535 : Nat := 4983230072969 + 3 ^ 40 * 1574535 * 2
def baseEnd_1574535 : Nat := 359330338812045492565045

theorem tailTrace_1574535 : CollatzResearch.WordTrace tailWord_1574535 prefixEnd_1574535 359330338812045492565045 := by
  unfold tailWord_1574535
  simp only [CollatzResearch.WordTrace]
  refine ⟨57428009350736079014157059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38285339567157386009438039 57428009350736079014157059)
  ·
    refine ⟨86142014026104118521235589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57428009350736079014157059 86142014026104118521235589)
    ·
      refine ⟨16151627629894522222731673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86142014026104118521235589 16151627629894522222731673)
      ·
        refine ⟨12113720722420891667048755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16151627629894522222731673 12113720722420891667048755)
        ·
          refine ⟨18170581083631337500573133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12113720722420891667048755 18170581083631337500573133)
          ·
            refine ⟨6813967906361751562714925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18170581083631337500573133 6813967906361751562714925)
            ·
              refine ⟨2555237964885656836018097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6813967906361751562714925 2555237964885656836018097)
              ·
                refine ⟨1916428473664242627013573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2555237964885656836018097 1916428473664242627013573)
                ·
                  refine ⟨359330338812045492565045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916428473664242627013573 359330338812045492565045)
                  ·
                    rfl

theorem cell21_1574535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_1574535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574535 prefixEnd_1574535 := by exact prefixLift 1574535
  have htrace : WordTrace (prefixWord ++ tailWord_1574535) baseStart_1574535 baseEnd_1574535 := by
    simpa [prefixWord, tailWord_1574535, baseEnd_1574535] using wordTrace_append hprefix tailTrace_1574535
  have hstable : (prefixWord ++ tailWord_1574535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574535).length < 2 ^ (prefixWord ++ tailWord_1574535).sum := by decide
  have hdescent : baseEnd_1574535 < baseStart_1574535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574552 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 4]
def baseStart_1574552 : Nat := 118140960795 + 1574552 * 2 ^ 59
def prefixEnd_1574552 : Nat := 4983230072969 + 3 ^ 40 * 1574552 * 2
def baseEnd_1574552 : Nat := 359334218443657240781677

theorem tailTrace_1574552 : CollatzResearch.WordTrace tailWord_1574552 prefixEnd_1574552 359334218443657240781677 := by
  unfold tailWord_1574552
  simp only [CollatzResearch.WordTrace]
  refine ⟨28714314695837245458762955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38285752927782993945017273 28714314695837245458762955)
  ·
    refine ⟨43071472043755868188144433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28714314695837245458762955 43071472043755868188144433)
    ·
      refine ⟨32303604032816901141108325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43071472043755868188144433 32303604032816901141108325)
      ·
        refine ⟨6056925756153168963957811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32303604032816901141108325 6056925756153168963957811)
        ·
          refine ⟨9085388634229753445936717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6056925756153168963957811 9085388634229753445936717)
          ·
            refine ⟨3407020737836157542226269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9085388634229753445936717 3407020737836157542226269)
            ·
              refine ⟨1277632776688559078334851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3407020737836157542226269 1277632776688559078334851)
              ·
                refine ⟨1916449165032838617502277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277632776688559078334851 1916449165032838617502277)
                ·
                  refine ⟨359334218443657240781677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1916449165032838617502277 359334218443657240781677)
                  ·
                    rfl

theorem cell21_1574552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_1574552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574552 prefixEnd_1574552 := by exact prefixLift 1574552
  have htrace : WordTrace (prefixWord ++ tailWord_1574552) baseStart_1574552 baseEnd_1574552 := by
    simpa [prefixWord, tailWord_1574552, baseEnd_1574552] using wordTrace_append hprefix tailTrace_1574552
  have hstable : (prefixWord ++ tailWord_1574552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574552).length < 2 ^ (prefixWord ++ tailWord_1574552).sum := by decide
  have hdescent : baseEnd_1574552 < baseStart_1574552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574563 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_1574563 : Nat := 118140960795 + 1574563 * 2 ^ 59
def prefixEnd_1574563 : Nat := 4983230072969 + 3 ^ 40 * 1574563 * 2
def baseEnd_1574563 : Nat := 359336728793523666098321

theorem tailTrace_1574563 : CollatzResearch.WordTrace tailWord_1574563 prefixEnd_1574563 359336728793523666098321 := by
  unfold tailWord_1574563
  simp only [CollatzResearch.WordTrace]
  refine ⟨57429030594634639796176343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38286020396423093197450895 57429030594634639796176343)
  ·
    refine ⟨86143545891951959694264515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57429030594634639796176343 86143545891951959694264515)
    ·
      refine ⟨129215318837927939541396773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86143545891951959694264515 129215318837927939541396773)
      ·
        refine ⟨24227872282111488664011895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129215318837927939541396773 24227872282111488664011895)
        ·
          refine ⟨36341808423167232996017843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24227872282111488664011895 36341808423167232996017843)
          ·
            refine ⟨54512712634750849494026765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36341808423167232996017843 54512712634750849494026765)
            ·
              refine ⟨20442267238031568560260037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54512712634750849494026765 20442267238031568560260037)
              ·
                refine ⟨3832925107130919105048757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20442267238031568560260037 3832925107130919105048757)
                ·
                  refine ⟨359336728793523666098321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3832925107130919105048757 359336728793523666098321)
                  ·
                    rfl

theorem cell21_1574563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_1574563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574563 prefixEnd_1574563 := by exact prefixLift 1574563
  have htrace : WordTrace (prefixWord ++ tailWord_1574563) baseStart_1574563 baseEnd_1574563 := by
    simpa [prefixWord, tailWord_1574563, baseEnd_1574563] using wordTrace_append hprefix tailTrace_1574563
  have hstable : (prefixWord ++ tailWord_1574563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574563).length < 2 ^ (prefixWord ++ tailWord_1574563).sum := by decide
  have hdescent : baseEnd_1574563 < baseStart_1574563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574656 : List Nat := [2, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_1574656 : Nat := 118140960795 + 1574656 * 2 ^ 59
def prefixEnd_1574656 : Nat := 4983230072969 + 3 ^ 40 * 1574656 * 2
def baseEnd_1574656 : Nat := 359357952660576171048131

theorem tailTrace_1574656 : CollatzResearch.WordTrace tailWord_1574656 prefixEnd_1574656 359357952660576171048131 := by
  unfold tailWord_1574656
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716211291648858339655911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38288281722198477786207881 28716211291648858339655911)
  ·
    refine ⟨43074316937473287509483867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28716211291648858339655911 43074316937473287509483867)
    ·
      refine ⟨64611475406209931264225801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43074316937473287509483867 64611475406209931264225801)
      ·
        refine ⟨48458606554657448448169351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64611475406209931264225801 48458606554657448448169351)
        ·
          refine ⟨72687909831986172672254027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48458606554657448448169351 72687909831986172672254027)
          ·
            refine ⟨109031864747979259008381041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72687909831986172672254027 109031864747979259008381041)
            ·
              refine ⟨81773898560984444256285781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109031864747979259008381041 81773898560984444256285781)
              ·
                refine ⟨958287873761536456128349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 81773898560984444256285781 958287873761536456128349)
                ·
                  refine ⟨359357952660576171048131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958287873761536456128349 359357952660576171048131)
                  ·
                    rfl

theorem cell21_1574656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_1574656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574656 prefixEnd_1574656 := by exact prefixLift 1574656
  have htrace : WordTrace (prefixWord ++ tailWord_1574656) baseStart_1574656 baseEnd_1574656 := by
    simpa [prefixWord, tailWord_1574656, baseEnd_1574656] using wordTrace_append hprefix tailTrace_1574656
  have hstable : (prefixWord ++ tailWord_1574656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574656).length < 2 ^ (prefixWord ++ tailWord_1574656).sum := by decide
  have hdescent : baseEnd_1574656 < baseStart_1574656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574870 : List Nat := [5, 2, 1, 1, 3, 1, 8]
def baseStart_1574870 : Nat := 118140960795 + 1574870 * 2 ^ 59
def prefixEnd_1574870 : Nat := 4983230072969 + 3 ^ 40 * 1574870 * 2
def baseEnd_1574870 : Nat := 39934087819573261609003

theorem tailTrace_1574870 : CollatzResearch.WordTrace tailWord_1574870 prefixEnd_1574870 39934087819573261609003 := by
  unfold tailWord_1574870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590014237782651951725129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38293485203014954151734709 3590014237782651951725129)
  ·
    refine ⟨2692510678336988963793847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3590014237782651951725129 2692510678336988963793847)
    ·
      refine ⟨4038766017505483445690771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692510678336988963793847 4038766017505483445690771)
      ·
        refine ⟨6058149026258225168536157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038766017505483445690771 6058149026258225168536157)
        ·
          refine ⟨2271805884846834438201059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058149026258225168536157 2271805884846834438201059)
          ·
            refine ⟨3407708827270251657301589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271805884846834438201059 3407708827270251657301589)
            ·
              refine ⟨39934087819573261609003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3407708827270251657301589 39934087819573261609003)
              ·
                rfl

theorem cell21_1574870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 8].length) (baseStart_1574870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574870 prefixEnd_1574870 := by exact prefixLift 1574870
  have htrace : WordTrace (prefixWord ++ tailWord_1574870) baseStart_1574870 baseEnd_1574870 := by
    simpa [prefixWord, tailWord_1574870, baseEnd_1574870] using wordTrace_append hprefix tailTrace_1574870
  have hstable : (prefixWord ++ tailWord_1574870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574870).length < 2 ^ (prefixWord ++ tailWord_1574870).sum := by decide
  have hdescent : baseEnd_1574870 < baseStart_1574870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1574884 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_1574884 : Nat := 118140960795 + 1574884 * 2 ^ 59
def prefixEnd_1574884 : Nat := 4983230072969 + 3 ^ 40 * 1574884 * 2
def baseEnd_1574884 : Nat := 359409985366898441247665

theorem tailTrace_1574884 : CollatzResearch.WordTrace tailWord_1574884 prefixEnd_1574884 359409985366898441247665 := by
  unfold tailWord_1574884
  simp only [CollatzResearch.WordTrace]
  refine ⟨28720369213235855809305853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38293825617647807745741137 28720369213235855809305853)
  ·
    refine ⟨10770138454963445928489695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28720369213235855809305853 10770138454963445928489695)
    ·
      refine ⟨16155207682445168892734543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10770138454963445928489695 16155207682445168892734543)
      ·
        refine ⟨24232811523667753339101815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16155207682445168892734543 24232811523667753339101815)
        ·
          refine ⟨36349217285501630008652723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24232811523667753339101815 36349217285501630008652723)
          ·
            refine ⟨54523825928252445012979085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36349217285501630008652723 54523825928252445012979085)
            ·
              refine ⟨20446434723094666879867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54523825928252445012979085 20446434723094666879867157)
              ·
                refine ⟨958426627645062509993773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20446434723094666879867157 958426627645062509993773)
                ·
                  refine ⟨359409985366898441247665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958426627645062509993773 359409985366898441247665)
                  ·
                    rfl

theorem cell21_1574884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_1574884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1574884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1574884 prefixEnd_1574884 := by exact prefixLift 1574884
  have htrace : WordTrace (prefixWord ++ tailWord_1574884) baseStart_1574884 baseEnd_1574884 := by
    simpa [prefixWord, tailWord_1574884, baseEnd_1574884] using wordTrace_append hprefix tailTrace_1574884
  have hstable : (prefixWord ++ tailWord_1574884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1574884).length < 2 ^ (prefixWord ++ tailWord_1574884).sum := by decide
  have hdescent : baseEnd_1574884 < baseStart_1574884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1574884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575036 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 3]
def baseStart_1575036 : Nat := 118140960795 + 1575036 * 2 ^ 59
def prefixEnd_1575036 : Nat := 4983230072969 + 3 ^ 40 * 1575036 * 2
def baseEnd_1575036 : Nat := 359444673837779954714021

theorem tailTrace_1575036 : CollatzResearch.WordTrace tailWord_1575036 prefixEnd_1575036 359444673837779954714021 := by
  unfold tailWord_1575036
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723141160960520789072481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38297521547947361052096641 28723141160960520789072481)
  ·
    refine ⟨21542355870720390591804361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28723141160960520789072481 21542355870720390591804361)
    ·
      refine ⟨16156766903040292943853271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21542355870720390591804361 16156766903040292943853271)
      ·
        refine ⟨24235150354560439415779907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16156766903040292943853271 24235150354560439415779907)
        ·
          refine ⟨36352725531840659123669861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24235150354560439415779907 36352725531840659123669861)
          ·
            refine ⟨6816136037220123585688099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36352725531840659123669861 6816136037220123585688099)
            ·
              refine ⟨10224204055830185378532149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816136037220123585688099 10224204055830185378532149)
              ·
                refine ⟨958519130234079879237389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10224204055830185378532149 958519130234079879237389)
                ·
                  refine ⟨359444673837779954714021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958519130234079879237389 359444673837779954714021)
                  ·
                    rfl

theorem cell21_1575036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_1575036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575036 prefixEnd_1575036 := by exact prefixLift 1575036
  have htrace : WordTrace (prefixWord ++ tailWord_1575036) baseStart_1575036 baseEnd_1575036 := by
    simpa [prefixWord, tailWord_1575036, baseEnd_1575036] using wordTrace_append hprefix tailTrace_1575036
  have hstable : (prefixWord ++ tailWord_1575036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575036).length < 2 ^ (prefixWord ++ tailWord_1575036).sum := by decide
  have hdescent : baseEnd_1575036 < baseStart_1575036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575050 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1575050 : Nat := 118140960795 + 1575050 * 2 ^ 59
def prefixEnd_1575050 : Nat := 4983230072969 + 3 ^ 40 * 1575050 * 2
def baseEnd_1575050 : Nat := 359447868828519041480659

theorem tailTrace_1575050 : CollatzResearch.WordTrace tailWord_1575050 prefixEnd_1575050 359447868828519041480659 := by
  unfold tailWord_1575050
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361698235967580492288651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38297861962580214646103069 14361698235967580492288651)
  ·
    refine ⟨21542547353951370738432977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14361698235967580492288651 21542547353951370738432977)
    ·
      refine ⟨16156910515463528053824733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21542547353951370738432977 16156910515463528053824733)
      ·
        refine ⟨6058841443298823020184275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16156910515463528053824733 6058841443298823020184275)
        ·
          refine ⟨9088262164948234530276413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058841443298823020184275 9088262164948234530276413)
          ·
            refine ⟨3408098311855587948853655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9088262164948234530276413 3408098311855587948853655)
            ·
              refine ⟨5112147467783381923280483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408098311855587948853655 5112147467783381923280483)
              ·
                refine ⟨7668221201675072884920725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112147467783381923280483 7668221201675072884920725)
                ·
                  refine ⟨359447868828519041480659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7668221201675072884920725 359447868828519041480659)
                  ·
                    rfl

theorem cell21_1575050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1575050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575050 prefixEnd_1575050 := by exact prefixLift 1575050
  have htrace : WordTrace (prefixWord ++ tailWord_1575050) baseStart_1575050 baseEnd_1575050 := by
    simpa [prefixWord, tailWord_1575050, baseEnd_1575050] using wordTrace_append hprefix tailTrace_1575050
  have hstable : (prefixWord ++ tailWord_1575050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575050).length < 2 ^ (prefixWord ++ tailWord_1575050).sum := by decide
  have hdescent : baseEnd_1575050 < baseStart_1575050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575109 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1575109 : Nat := 118140960795 + 1575109 * 2 ^ 59
def prefixEnd_1575109 : Nat := 4983230072969 + 3 ^ 40 * 1575109 * 2
def baseEnd_1575109 : Nat := 359461333432348049997205

theorem tailTrace_1575109 : CollatzResearch.WordTrace tailWord_1575109 prefixEnd_1575109 359461333432348049997205 := by
  unfold tailWord_1575109
  simp only [CollatzResearch.WordTrace]
  refine ⟨57448944850656575045552381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38299296567104383363701587 57448944850656575045552381)
  ·
    refine ⟨21543354318996215642082143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57448944850656575045552381 21543354318996215642082143)
    ·
      refine ⟨32315031478494323463123215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21543354318996215642082143 32315031478494323463123215)
      ·
        refine ⟨48472547217741485194684823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32315031478494323463123215 48472547217741485194684823)
        ·
          refine ⟨72708820826612227792027235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48472547217741485194684823 72708820826612227792027235)
          ·
            refine ⟨109063231239918341688040853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72708820826612227792027235 109063231239918341688040853)
            ·
              refine ⟨5112338964371172266626915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109063231239918341688040853 5112338964371172266626915)
              ·
                refine ⟨7668508446556758399940373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112338964371172266626915 7668508446556758399940373)
                ·
                  refine ⟨359461333432348049997205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7668508446556758399940373 359461333432348049997205)
                  ·
                    rfl

theorem cell21_1575109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1575109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575109 prefixEnd_1575109 := by exact prefixLift 1575109
  have htrace : WordTrace (prefixWord ++ tailWord_1575109) baseStart_1575109 baseEnd_1575109 := by
    simpa [prefixWord, tailWord_1575109, baseEnd_1575109] using wordTrace_append hprefix tailTrace_1575109
  have hstable : (prefixWord ++ tailWord_1575109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575109).length < 2 ^ (prefixWord ++ tailWord_1575109).sum := by decide
  have hdescent : baseEnd_1575109 < baseStart_1575109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575205 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 3]
def baseStart_1575205 : Nat := 118140960795 + 1575205 * 2 ^ 59
def prefixEnd_1575205 : Nat := 4983230072969 + 3 ^ 40 * 1575205 * 2
def baseEnd_1575205 : Nat := 359483241940273216397009

theorem tailTrace_1575205 : CollatzResearch.WordTrace tailWord_1575205 prefixEnd_1575205 359483241940273216397009 := by
  unfold tailWord_1575205
  simp only [CollatzResearch.WordTrace]
  refine ⟨57452446258308783441047069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38301630838872522294031379 57452446258308783441047069)
  ·
    refine ⟨21544667346865793790392651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57452446258308783441047069 21544667346865793790392651)
    ·
      refine ⟨32317001020298690685588977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21544667346865793790392651 32317001020298690685588977)
      ·
        refine ⟨24237750765224018014191733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32317001020298690685588977 24237750765224018014191733)
        ·
          refine ⟨2272289134239751688830475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24237750765224018014191733 2272289134239751688830475)
          ·
            refine ⟨3408433701359627533245713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272289134239751688830475 3408433701359627533245713)
            ·
              refine ⟨2556325276019720649934285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408433701359627533245713 2556325276019720649934285)
              ·
                refine ⟨958621978507395243725357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2556325276019720649934285 958621978507395243725357)
                ·
                  refine ⟨359483241940273216397009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958621978507395243725357 359483241940273216397009)
                  ·
                    rfl

theorem cell21_1575205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_1575205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575205 prefixEnd_1575205 := by exact prefixLift 1575205
  have htrace : WordTrace (prefixWord ++ tailWord_1575205) baseStart_1575205 baseEnd_1575205 := by
    simpa [prefixWord, tailWord_1575205, baseEnd_1575205] using wordTrace_append hprefix tailTrace_1575205
  have hstable : (prefixWord ++ tailWord_1575205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575205).length < 2 ^ (prefixWord ++ tailWord_1575205).sum := by decide
  have hdescent : baseEnd_1575205 < baseStart_1575205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575399 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_1575399 : Nat := 118140960795 + 1575399 * 2 ^ 59
def prefixEnd_1575399 : Nat := 4983230072969 + 3 ^ 40 * 1575399 * 2
def baseEnd_1575399 : Nat := 359527515383371990163279

theorem tailTrace_1575399 : CollatzResearch.WordTrace tailWord_1575399 prefixEnd_1575399 359527515383371990163279 := by
  unfold tailWord_1575399
  simp only [CollatzResearch.WordTrace]
  refine ⟨57459522019605954573609251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38306348013070636382406167 57459522019605954573609251)
  ·
    refine ⟨86189283029408931860413877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57459522019605954573609251 86189283029408931860413877)
    ·
      refine ⟨8080245284007087361913801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86189283029408931860413877 8080245284007087361913801)
      ·
        refine ⟨6060183963005315521435351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8080245284007087361913801 6060183963005315521435351)
        ·
          refine ⟨9090275944507973282153027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060183963005315521435351 9090275944507973282153027)
          ·
            refine ⟨13635413916761959923229541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090275944507973282153027 13635413916761959923229541)
            ·
              refine ⟨2556640109392867485605539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13635413916761959923229541 2556640109392867485605539)
              ·
                refine ⟨3834960164089301228408309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556640109392867485605539 3834960164089301228408309)
                ·
                  refine ⟨359527515383371990163279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834960164089301228408309 359527515383371990163279)
                  ·
                    rfl

theorem cell21_1575399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_1575399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575399 prefixEnd_1575399 := by exact prefixLift 1575399
  have htrace : WordTrace (prefixWord ++ tailWord_1575399) baseStart_1575399 baseEnd_1575399 := by
    simpa [prefixWord, tailWord_1575399, baseEnd_1575399] using wordTrace_append hprefix tailTrace_1575399
  have hstable : (prefixWord ++ tailWord_1575399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575399).length < 2 ^ (prefixWord ++ tailWord_1575399).sum := by decide
  have hdescent : baseEnd_1575399 < baseStart_1575399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575427 : List Nat := [1, 1, 1, 3, 2, 1, 5, 7]
def baseStart_1575427 : Nat := 118140960795 + 1575427 * 2 ^ 59
def prefixEnd_1575427 : Nat := 4983230072969 + 3 ^ 40 * 1575427 * 2
def baseEnd_1575427 : Nat := 119844635121616721232185

theorem tailTrace_1575427 : CollatzResearch.WordTrace tailWord_1575427 prefixEnd_1575427 119844635121616721232185 := by
  unfold tailWord_1575427
  simp only [CollatzResearch.WordTrace]
  refine ⟨57460543263504515355628535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38307028842336343570419023 57460543263504515355628535)
  ·
    refine ⟨86190814895256773033442803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57460543263504515355628535 86190814895256773033442803)
    ·
      refine ⟨129286222342885159550164205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86190814895256773033442803 129286222342885159550164205)
      ·
        refine ⟨48482333378581934831311577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129286222342885159550164205 48482333378581934831311577)
        ·
          refine ⟨36361750033936451123483683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48482333378581934831311577 36361750033936451123483683)
          ·
            refine ⟨54542625050904676685225525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36361750033936451123483683 54542625050904676685225525)
            ·
              refine ⟨5113371098522313439239893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54542625050904676685225525 5113371098522313439239893)
              ·
                refine ⟨119844635121616721232185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5113371098522313439239893 119844635121616721232185)
                ·
                  rfl

theorem cell21_1575427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_1575427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575427 prefixEnd_1575427 := by exact prefixLift 1575427
  have htrace : WordTrace (prefixWord ++ tailWord_1575427) baseStart_1575427 baseEnd_1575427 := by
    simpa [prefixWord, tailWord_1575427, baseEnd_1575427] using wordTrace_append hprefix tailTrace_1575427
  have hstable : (prefixWord ++ tailWord_1575427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575427).length < 2 ^ (prefixWord ++ tailWord_1575427).sum := by decide
  have hdescent : baseEnd_1575427 < baseStart_1575427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575464 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 4]
def baseStart_1575464 : Nat := 118140960795 + 1575464 * 2 ^ 59
def prefixEnd_1575464 : Nat := 4983230072969 + 3 ^ 40 * 1575464 * 2
def baseEnd_1575464 : Nat := 359542349268946321579813

theorem tailTrace_1575464 : CollatzResearch.WordTrace tailWord_1575464 prefixEnd_1575464 359542349268946321579813 := by
  unfold tailWord_1575464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28730946382185235337362723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38307928509580313783150297 28730946382185235337362723)
  ·
    refine ⟨43096419573277853006044085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28730946382185235337362723 43096419573277853006044085)
    ·
      refine ⟨4040289334994798719316633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43096419573277853006044085 4040289334994798719316633)
      ·
        refine ⟨3030217001246099039487475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4040289334994798719316633 3030217001246099039487475)
        ·
          refine ⟨4545325501869148559231213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3030217001246099039487475 4545325501869148559231213)
          ·
            refine ⟨1704497063200930709711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4545325501869148559231213 1704497063200930709711705)
            ·
              refine ⟨1278372797400698032283779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704497063200930709711705 1278372797400698032283779)
              ·
                refine ⟨1917559196101047048425669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278372797400698032283779 1917559196101047048425669)
                ·
                  refine ⟨359542349268946321579813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917559196101047048425669 359542349268946321579813)
                  ·
                    rfl

theorem cell21_1575464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_1575464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575464 prefixEnd_1575464 := by exact prefixLift 1575464
  have htrace : WordTrace (prefixWord ++ tailWord_1575464) baseStart_1575464 baseEnd_1575464 := by
    simpa [prefixWord, tailWord_1575464, baseEnd_1575464] using wordTrace_append hprefix tailTrace_1575464
  have hstable : (prefixWord ++ tailWord_1575464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575464).length < 2 ^ (prefixWord ++ tailWord_1575464).sum := by decide
  have hdescent : baseEnd_1575464 < baseStart_1575464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575506 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1575506 : Nat := 118140960795 + 1575506 * 2 ^ 59
def prefixEnd_1575506 : Nat := 4983230072969 + 3 ^ 40 * 1575506 * 2
def baseEnd_1575506 : Nat := 359551934241163581879727

theorem tailTrace_1575506 : CollatzResearch.WordTrace tailWord_1575506 prefixEnd_1575506 359551934241163581879727 := by
  unfold tailWord_1575506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365856157554577961938593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38308949753478874565169581 14365856157554577961938593)
  ·
    refine ⟨10774392118165933471453945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14365856157554577961938593 10774392118165933471453945)
    ·
      refine ⟨8080794088624450103590459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10774392118165933471453945 8080794088624450103590459)
      ·
        refine ⟨12121191132936675155385689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8080794088624450103590459 12121191132936675155385689)
        ·
          refine ⟨9090893349702506366539267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12121191132936675155385689 9090893349702506366539267)
          ·
            refine ⟨13636340024553759549808901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090893349702506366539267 13636340024553759549808901)
            ·
              refine ⟨2556813754603829915589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13636340024553759549808901 2556813754603829915589169)
              ·
                refine ⟨1917610315952872436691877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556813754603829915589169 1917610315952872436691877)
                ·
                  refine ⟨359551934241163581879727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917610315952872436691877 359551934241163581879727)
                  ·
                    rfl

theorem cell21_1575506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1575506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575506 prefixEnd_1575506 := by exact prefixLift 1575506
  have htrace : WordTrace (prefixWord ++ tailWord_1575506) baseStart_1575506 baseEnd_1575506 := by
    simpa [prefixWord, tailWord_1575506, baseEnd_1575506] using wordTrace_append hprefix tailTrace_1575506
  have hstable : (prefixWord ++ tailWord_1575506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575506).length < 2 ^ (prefixWord ++ tailWord_1575506).sum := by decide
  have hdescent : baseEnd_1575506 < baseStart_1575506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575641 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_1575641 : Nat := 118140960795 + 1575641 * 2 ^ 59
def prefixEnd_1575641 : Nat := 4983230072969 + 3 ^ 40 * 1575641 * 2
def baseEnd_1575641 : Nat := 359582743080433347129451

theorem tailTrace_1575641 : CollatzResearch.WordTrace tailWord_1575641 prefixEnd_1575641 359582743080433347129451 := by
  unfold tailWord_1575641
  simp only [CollatzResearch.WordTrace]
  refine ⟨57468348484729229903918777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38312232323152819935945851 57468348484729229903918777)
  ·
    refine ⟨43101261363546922427939083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57468348484729229903918777 43101261363546922427939083)
    ·
      refine ⟨64651892045320383641908625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43101261363546922427939083 64651892045320383641908625)
      ·
        refine ⟨48488919033990287731431469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64651892045320383641908625 48488919033990287731431469)
        ·
          refine ⟨18183344637746357899286801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48488919033990287731431469 18183344637746357899286801)
          ·
            refine ⟨13637508478309768424465101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18183344637746357899286801 13637508478309768424465101)
            ·
              refine ⟨5114065679366163159174413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13637508478309768424465101 5114065679366163159174413)
              ·
                refine ⟨1917774629762311184690405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5114065679366163159174413 1917774629762311184690405)
                ·
                  refine ⟨359582743080433347129451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1917774629762311184690405 359582743080433347129451)
                  ·
                    rfl

theorem cell21_1575641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_1575641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575641 prefixEnd_1575641 := by exact prefixLift 1575641
  have htrace : WordTrace (prefixWord ++ tailWord_1575641) baseStart_1575641 baseEnd_1575641 := by
    simpa [prefixWord, tailWord_1575641, baseEnd_1575641] using wordTrace_append hprefix tailTrace_1575641
  have hstable : (prefixWord ++ tailWord_1575641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575641).length < 2 ^ (prefixWord ++ tailWord_1575641).sum := by decide
  have hdescent : baseEnd_1575641 < baseStart_1575641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575678 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1575678 : Nat := 118140960795 + 1575678 * 2 ^ 59
def prefixEnd_1575678 : Nat := 4983230072969 + 3 ^ 40 * 1575678 * 2
def baseEnd_1575678 : Nat := 359591186984529505012709

theorem tailTrace_1575678 : CollatzResearch.WordTrace tailWord_1575678 prefixEnd_1575678 359591186984529505012709 := by
  unfold tailWord_1575678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7183712248199398152876961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38313131990396790148677125 7183712248199398152876961)
  ·
    refine ⟨5387784186149548614657721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7183712248199398152876961 5387784186149548614657721)
    ·
      refine ⟨4040838139612161460993291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5387784186149548614657721 4040838139612161460993291)
      ·
        refine ⟨6061257209418242191489937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040838139612161460993291 6061257209418242191489937)
        ·
          refine ⟨4545942907063681643617453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6061257209418242191489937 4545942907063681643617453)
          ·
            refine ⟨1704728590148880616356545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4545942907063681643617453 1704728590148880616356545)
            ·
              refine ⟨1278546442611660462267409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1704728590148880616356545 1278546442611660462267409)
              ·
                refine ⟨958909831958745346700557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278546442611660462267409 958909831958745346700557)
                ·
                  refine ⟨359591186984529505012709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958909831958745346700557 359591186984529505012709)
                  ·
                    rfl

theorem cell21_1575678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1575678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575678 prefixEnd_1575678 := by exact prefixLift 1575678
  have htrace : WordTrace (prefixWord ++ tailWord_1575678) baseStart_1575678 baseEnd_1575678 := by
    simpa [prefixWord, tailWord_1575678, baseEnd_1575678] using wordTrace_append hprefix tailTrace_1575678
  have hstable : (prefixWord ++ tailWord_1575678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575678).length < 2 ^ (prefixWord ++ tailWord_1575678).sum := by decide
  have hdescent : baseEnd_1575678 < baseStart_1575678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575703 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_1575703 : Nat := 118140960795 + 1575703 * 2 ^ 59
def prefixEnd_1575703 : Nat := 4983230072969 + 3 ^ 40 * 1575703 * 2
def baseEnd_1575703 : Nat := 359596892325135017095991

theorem tailTrace_1575703 : CollatzResearch.WordTrace tailWord_1575703 prefixEnd_1575703 359596892325135017095991 := by
  unfold tailWord_1575703
  simp only [CollatzResearch.WordTrace]
  refine ⟨57470609810504614492675763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38313739873669742995117175 57470609810504614492675763)
  ·
    refine ⟨86205914715756921739013645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57470609810504614492675763 86205914715756921739013645)
    ·
      refine ⟨32327218018408845652130117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86205914715756921739013645 32327218018408845652130117)
      ·
        refine ⟨6061353378451658559774397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32327218018408845652130117 6061353378451658559774397)
        ·
          refine ⟨2273007516919371959915399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6061353378451658559774397 2273007516919371959915399)
          ·
            refine ⟨3409511275379057939873099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273007516919371959915399 3409511275379057939873099)
            ·
              refine ⟨5114266913068586909809649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3409511275379057939873099 5114266913068586909809649)
              ·
                refine ⟨3835700184801440182357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114266913068586909809649 3835700184801440182357237)
                ·
                  refine ⟨359596892325135017095991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3835700184801440182357237 359596892325135017095991)
                  ·
                    rfl

theorem cell21_1575703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_1575703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575703 prefixEnd_1575703 := by exact prefixLift 1575703
  have htrace : WordTrace (prefixWord ++ tailWord_1575703) baseStart_1575703 baseEnd_1575703 := by
    simpa [prefixWord, tailWord_1575703, baseEnd_1575703] using wordTrace_append hprefix tailTrace_1575703
  have hstable : (prefixWord ++ tailWord_1575703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575703).length < 2 ^ (prefixWord ++ tailWord_1575703).sum := by decide
  have hdescent : baseEnd_1575703 < baseStart_1575703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575720 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 3]
def baseStart_1575720 : Nat := 118140960795 + 1575720 * 2 ^ 59
def prefixEnd_1575720 : Nat := 4983230072969 + 3 ^ 40 * 1575720 * 2
def baseEnd_1575720 : Nat := 359600771956746765312623

theorem tailTrace_1575720 : CollatzResearch.WordTrace tailWord_1575720 prefixEnd_1575720 359600771956746765312623 := by
  unfold tailWord_1575720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28735614925721513198022307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38314153234295350930696409 28735614925721513198022307)
  ·
    refine ⟨43103422388582269797033461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28735614925721513198022307 43103422388582269797033461)
    ·
      refine ⟨4040945848929587793471887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43103422388582269797033461 4040945848929587793471887)
      ·
        refine ⟨6061418773394381690207831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040945848929587793471887 6061418773394381690207831)
        ·
          refine ⟨9092128160091572535311747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061418773394381690207831 9092128160091572535311747)
          ·
            refine ⟨13638192240137358802967621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092128160091572535311747 13638192240137358802967621)
            ·
              refine ⟨2557161045025754775556429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13638192240137358802967621 2557161045025754775556429)
              ·
                refine ⟨958935391884658040833661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2557161045025754775556429 958935391884658040833661)
                ·
                  refine ⟨359600771956746765312623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 958935391884658040833661 359600771956746765312623)
                  ·
                    rfl

theorem cell21_1575720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_1575720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575720 prefixEnd_1575720 := by exact prefixLift 1575720
  have htrace : WordTrace (prefixWord ++ tailWord_1575720) baseStart_1575720 baseEnd_1575720 := by
    simpa [prefixWord, tailWord_1575720, baseEnd_1575720] using wordTrace_append hprefix tailTrace_1575720
  have hstable : (prefixWord ++ tailWord_1575720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575720).length < 2 ^ (prefixWord ++ tailWord_1575720).sum := by decide
  have hdescent : baseEnd_1575720 < baseStart_1575720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575731 : List Nat := [1, 1, 1, 2, 6, 2, 8]
def baseStart_1575731 : Nat := 118140960795 + 1575731 * 2 ^ 59
def prefixEnd_1575731 : Nat := 4983230072969 + 3 ^ 40 * 1575731 * 2
def baseEnd_1575731 : Nat := 39955920256290354514363

theorem tailTrace_1575731 : CollatzResearch.WordTrace tailWord_1575731 prefixEnd_1575731 39955920256290354514363 := by
  unfold tailWord_1575731
  simp only [CollatzResearch.WordTrace]
  refine ⟨57471631054403175274695047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38314420702935450183130031 57471631054403175274695047)
  ·
    refine ⟨86207446581604762912042571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57471631054403175274695047 86207446581604762912042571)
    ·
      refine ⟨129311169872407144368063857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86207446581604762912042571 129311169872407144368063857)
      ·
        refine ⟨96983377404305358276047893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129311169872407144368063857 96983377404305358276047893)
        ·
          refine ⟨4546095815826813669189745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96983377404305358276047893 4546095815826813669189745)
          ·
            refine ⟨3409571861870110251892309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546095815826813669189745 3409571861870110251892309)
            ·
              refine ⟨39955920256290354514363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3409571861870110251892309 39955920256290354514363)
              ·
                rfl

theorem cell21_1575731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_1575731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575731 prefixEnd_1575731 := by exact prefixLift 1575731
  have htrace : WordTrace (prefixWord ++ tailWord_1575731) baseStart_1575731 baseEnd_1575731 := by
    simpa [prefixWord, tailWord_1575731, baseEnd_1575731] using wordTrace_append hprefix tailTrace_1575731
  have hstable : (prefixWord ++ tailWord_1575731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575731).length < 2 ^ (prefixWord ++ tailWord_1575731).sum := by decide
  have hdescent : baseEnd_1575731 < baseStart_1575731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575762 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1575762 : Nat := 118140960795 + 1575762 * 2 ^ 59
def prefixEnd_1575762 : Nat := 4983230072969 + 3 ^ 40 * 1575762 * 2
def baseEnd_1575762 : Nat := 359610356928964025612537

theorem tailTrace_1575762 : CollatzResearch.WordTrace tailWord_1575762 prefixEnd_1575762 359610356928964025612537 := by
  unfold tailWord_1575762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14368190429322716892268385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38315174478193911712715693 14368190429322716892268385)
  ·
    refine ⟨10776142821992037669201289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14368190429322716892268385 10776142821992037669201289)
    ·
      refine ⟨8082107116494028251900967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10776142821992037669201289 8082107116494028251900967)
      ·
        refine ⟨12123160674741042377851451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082107116494028251900967 12123160674741042377851451)
        ·
          refine ⟨18184741012111563566777177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123160674741042377851451 18184741012111563566777177)
          ·
            refine ⟨13638555759083672675082883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18184741012111563566777177 13638555759083672675082883)
            ·
              refine ⟨20457833638625509012624325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638555759083672675082883 20457833638625509012624325)
              ·
                refine ⟨3835843807242282939867061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20457833638625509012624325 3835843807242282939867061)
                ·
                  refine ⟨359610356928964025612537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3835843807242282939867061 359610356928964025612537)
                  ·
                    rfl

theorem cell21_1575762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1575762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575762 prefixEnd_1575762 := by exact prefixLift 1575762
  have htrace : WordTrace (prefixWord ++ tailWord_1575762) baseStart_1575762 baseEnd_1575762 := by
    simpa [prefixWord, tailWord_1575762, baseEnd_1575762] using wordTrace_append hprefix tailTrace_1575762
  have hstable : (prefixWord ++ tailWord_1575762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575762).length < 2 ^ (prefixWord ++ tailWord_1575762).sum := by decide
  have hdescent : baseEnd_1575762 < baseStart_1575762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575776 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 8]
def baseStart_1575776 : Nat := 118140960795 + 1575776 * 2 ^ 59
def prefixEnd_1575776 : Nat := 4983230072969 + 3 ^ 40 * 1575776 * 2
def baseEnd_1575776 : Nat := 359613551919703112379175

theorem tailTrace_1575776 : CollatzResearch.WordTrace tailWord_1575776 prefixEnd_1575776 359613551919703112379175 := by
  unfold tailWord_1575776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736636169620073980041591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38315514892826765306722121 28736636169620073980041591)
  ·
    refine ⟨43104954254430110970062387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736636169620073980041591 43104954254430110970062387)
    ·
      refine ⟨64657431381645166455093581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43104954254430110970062387 64657431381645166455093581)
      ·
        refine ⟨24246536768116937420660093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64657431381645166455093581 24246536768116937420660093)
        ·
          refine ⟨9092451288043851532747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24246536768116937420660093 9092451288043851532747535)
          ·
            refine ⟨13638676932065777299121303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092451288043851532747535 13638676932065777299121303)
            ·
              refine ⟨20458015398098665948681955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638676932065777299121303 20458015398098665948681955)
              ·
                refine ⟨30687023097147998923022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20458015398098665948681955 30687023097147998923022933)
                ·
                  refine ⟨359613551919703112379175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30687023097147998923022933 359613551919703112379175)
                  ·
                    rfl

theorem cell21_1575776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_1575776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575776 prefixEnd_1575776 := by exact prefixLift 1575776
  have htrace : WordTrace (prefixWord ++ tailWord_1575776) baseStart_1575776 baseEnd_1575776 := by
    simpa [prefixWord, tailWord_1575776, baseEnd_1575776] using wordTrace_append hprefix tailTrace_1575776
  have hstable : (prefixWord ++ tailWord_1575776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575776).length < 2 ^ (prefixWord ++ tailWord_1575776).sum := by decide
  have hdescent : baseEnd_1575776 < baseStart_1575776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575903 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 4]
def baseStart_1575903 : Nat := 118140960795 + 1575903 * 2 ^ 59
def prefixEnd_1575903 : Nat := 4983230072969 + 3 ^ 40 * 1575903 * 2
def baseEnd_1575903 : Nat := 359642535049979113762249

theorem tailTrace_1575903 : CollatzResearch.WordTrace tailWord_1575903 prefixEnd_1575903 359642535049979113762249 := by
  unfold tailWord_1575903
  simp only [CollatzResearch.WordTrace]
  refine ⟨57477904409780048649956363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38318602939853365766637575 57477904409780048649956363)
  ·
    refine ⟨86216856614670072974934545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57477904409780048649956363 86216856614670072974934545)
    ·
      refine ⟨64662642461002554731200909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86216856614670072974934545 64662642461002554731200909)
      ·
        refine ⟨24248490922875958024200341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64662642461002554731200909 24248490922875958024200341)
        ·
          refine ⟨1136648012009810532384391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24248490922875958024200341 1136648012009810532384391)
          ·
            refine ⟨1704972018014715798576587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136648012009810532384391 1704972018014715798576587)
            ·
              refine ⟨2557458027022073697864881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704972018014715798576587 2557458027022073697864881)
              ·
                refine ⟨1918093520266555273398661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557458027022073697864881 1918093520266555273398661)
                ·
                  refine ⟨359642535049979113762249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918093520266555273398661 359642535049979113762249)
                  ·
                    rfl

theorem cell21_1575903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 4].length) (baseStart_1575903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575903 prefixEnd_1575903 := by exact prefixLift 1575903
  have htrace : WordTrace (prefixWord ++ tailWord_1575903) baseStart_1575903 baseEnd_1575903 := by
    simpa [prefixWord, tailWord_1575903, baseEnd_1575903] using wordTrace_append hprefix tailTrace_1575903
  have hstable : (prefixWord ++ tailWord_1575903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575903).length < 2 ^ (prefixWord ++ tailWord_1575903).sum := by decide
  have hdescent : baseEnd_1575903 < baseStart_1575903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575914 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1575914 : Nat := 118140960795 + 1575914 * 2 ^ 59
def prefixEnd_1575914 : Nat := 4983230072969 + 3 ^ 40 * 1575914 * 2
def baseEnd_1575914 : Nat := 359645045399845539078893

theorem tailTrace_1575914 : CollatzResearch.WordTrace tailWord_1575914 prefixEnd_1575914 359645045399845539078893 := by
  unfold tailWord_1575914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14369576403185049382151699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38318870408493465019071197 14369576403185049382151699)
  ·
    refine ⟨21554364604777574073227549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14369576403185049382151699 21554364604777574073227549)
    ·
      refine ⟨8082886726791590277460331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21554364604777574073227549 8082886726791590277460331)
      ·
        refine ⟨12124330090187385416190497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082886726791590277460331 12124330090187385416190497)
        ·
          refine ⟨9093247567640539062142873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12124330090187385416190497 9093247567640539062142873)
          ·
            refine ⟨6819935675730404296607155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9093247567640539062142873 6819935675730404296607155)
            ·
              refine ⟨10229903513595606444910733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819935675730404296607155 10229903513595606444910733)
              ·
                refine ⟨3836213817598352416841525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10229903513595606444910733 3836213817598352416841525)
                ·
                  refine ⟨359645045399845539078893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836213817598352416841525 359645045399845539078893)
                  ·
                    rfl

theorem cell21_1575914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1575914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575914 prefixEnd_1575914 := by exact prefixLift 1575914
  have htrace : WordTrace (prefixWord ++ tailWord_1575914) baseStart_1575914 baseEnd_1575914 := by
    simpa [prefixWord, tailWord_1575914, baseEnd_1575914] using wordTrace_append hprefix tailTrace_1575914
  have hstable : (prefixWord ++ tailWord_1575914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575914).length < 2 ^ (prefixWord ++ tailWord_1575914).sum := by decide
  have hdescent : baseEnd_1575914 < baseStart_1575914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575934 : List Nat := [4, 2, 2, 2, 2, 2, 2, 5]
def baseStart_1575934 : Nat := 118140960795 + 1575934 * 2 ^ 59
def prefixEnd_1575934 : Nat := 4983230072969 + 3 ^ 40 * 1575934 * 2
def baseEnd_1575934 : Nat := 119883203224109982915173

theorem tailTrace_1575934 : CollatzResearch.WordTrace tailWord_1575934 prefixEnd_1575934 119883203224109982915173 := by
  unfold tailWord_1575934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184879384083467618041857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38319356715111827296223237 7184879384083467618041857)
  ·
    refine ⟨5388659538062600713531393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7184879384083467618041857 5388659538062600713531393)
    ·
      refine ⟨4041494653546950535148545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5388659538062600713531393 4041494653546950535148545)
      ·
        refine ⟨3031120990160212901361409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4041494653546950535148545 3031120990160212901361409)
        ·
          refine ⟨2273340742620159676021057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031120990160212901361409 2273340742620159676021057)
          ·
            refine ⟨1705005556965119757015793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273340742620159676021057 1705005556965119757015793)
            ·
              refine ⟨1278754167723839817761845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705005556965119757015793 1278754167723839817761845)
              ·
                refine ⟨119883203224109982915173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1278754167723839817761845 119883203224109982915173)
                ·
                  rfl

theorem cell21_1575934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_1575934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575934 prefixEnd_1575934 := by exact prefixLift 1575934
  have htrace : WordTrace (prefixWord ++ tailWord_1575934) baseStart_1575934 baseEnd_1575934 := by
    simpa [prefixWord, tailWord_1575934, baseEnd_1575934] using wordTrace_append hprefix tailTrace_1575934
  have hstable : (prefixWord ++ tailWord_1575934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575934).length < 2 ^ (prefixWord ++ tailWord_1575934).sum := by decide
  have hdescent : baseEnd_1575934 < baseStart_1575934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575948 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 3]
def baseStart_1575948 : Nat := 118140960795 + 1575948 * 2 ^ 59
def prefixEnd_1575948 : Nat := 4983230072969 + 3 ^ 40 * 1575948 * 2
def baseEnd_1575948 : Nat := 359652804663069035512157

theorem tailTrace_1575948 : CollatzResearch.WordTrace tailWord_1575948 prefixEnd_1575948 359652804663069035512157 := by
  unfold tailWord_1575948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28739772847308510667672249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38319697129744680890229665 28739772847308510667672249)
  ·
    refine ⟨21554829635481383000754187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28739772847308510667672249 21554829635481383000754187)
    ·
      refine ⟨32332244453222074501131281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21554829635481383000754187 32332244453222074501131281)
      ·
        refine ⟨24249183339916555875848461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32332244453222074501131281 24249183339916555875848461)
        ·
          refine ⟨9093443752468708453443173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24249183339916555875848461 9093443752468708453443173)
          ·
            refine ⟨1705020703587882835020595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9093443752468708453443173 1705020703587882835020595)
            ·
              refine ⟨2557531055381824252530893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705020703587882835020595 2557531055381824252530893)
              ·
                refine ⟨959074145768184094699085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2557531055381824252530893 959074145768184094699085)
                ·
                  refine ⟨359652804663069035512157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959074145768184094699085 359652804663069035512157)
                  ·
                    rfl

theorem cell21_1575948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 3].length) (baseStart_1575948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575948 prefixEnd_1575948 := by exact prefixLift 1575948
  have htrace : WordTrace (prefixWord ++ tailWord_1575948) baseStart_1575948 baseEnd_1575948 := by
    simpa [prefixWord, tailWord_1575948, baseEnd_1575948] using wordTrace_append hprefix tailTrace_1575948
  have hstable : (prefixWord ++ tailWord_1575948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575948).length < 2 ^ (prefixWord ++ tailWord_1575948).sum := by decide
  have hdescent : baseEnd_1575948 < baseStart_1575948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575959 : List Nat := [1, 1, 3, 5, 1, 1, 9]
def baseStart_1575959 : Nat := 118140960795 + 1575959 * 2 ^ 59
def prefixEnd_1575959 : Nat := 4983230072969 + 3 ^ 40 * 1575959 * 2
def baseEnd_1575959 : Nat := 39961701668103940092089

theorem tailTrace_1575959 : CollatzResearch.WordTrace tailWord_1575959 prefixEnd_1575959 39961701668103940092089 := by
  unfold tailWord_1575959
  simp only [CollatzResearch.WordTrace]
  refine ⟨57479946897577170213994931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38319964598384780142663287 57479946897577170213994931)
  ·
    refine ⟨86219920346365755320992397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57479946897577170213994931 86219920346365755320992397)
    ·
      refine ⟨32332470129887158245372149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86219920346365755320992397 32332470129887158245372149)
      ·
        refine ⟨3031169074676921085503639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32332470129887158245372149 3031169074676921085503639)
        ·
          refine ⟨4546753612015381628255459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031169074676921085503639 4546753612015381628255459)
          ·
            refine ⟨6820130418023072442383189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546753612015381628255459 6820130418023072442383189)
            ·
              refine ⟨39961701668103940092089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6820130418023072442383189 39961701668103940092089)
              ·
                rfl

theorem cell21_1575959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_1575959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575959 prefixEnd_1575959 := by exact prefixLift 1575959
  have htrace : WordTrace (prefixWord ++ tailWord_1575959) baseStart_1575959 baseEnd_1575959 := by
    simpa [prefixWord, tailWord_1575959, baseEnd_1575959] using wordTrace_append hprefix tailTrace_1575959
  have hstable : (prefixWord ++ tailWord_1575959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575959).length < 2 ^ (prefixWord ++ tailWord_1575959).sum := by decide
  have hdescent : baseEnd_1575959 < baseStart_1575959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1575965 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1575965 : Nat := 118140960795 + 1575965 * 2 ^ 59
def prefixEnd_1575965 : Nat := 4983230072969 + 3 ^ 40 * 1575965 * 2
def baseEnd_1575965 : Nat := 359656684294680783728789

theorem tailTrace_1575965 : CollatzResearch.WordTrace tailWord_1575965 prefixEnd_1575965 359656684294680783728789 := by
  unfold tailWord_1575965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57480165735555433238713349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38320110490370288825808899 57480165735555433238713349)
  ·
    refine ⟨10777531075416643732258753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57480165735555433238713349 10777531075416643732258753)
    ·
      refine ⟨8083148306562482799194065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10777531075416643732258753 8083148306562482799194065)
      ·
        refine ⟨6062361229921862099395549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8083148306562482799194065 6062361229921862099395549)
        ·
          refine ⟨2273385461220698287273331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6062361229921862099395549 2273385461220698287273331)
          ·
            refine ⟨3410078191831047430909997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273385461220698287273331 3410078191831047430909997)
            ·
              refine ⟨1278779321936642786591249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3410078191831047430909997 1278779321936642786591249)
              ·
                refine ⟨959084491452482089943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278779321936642786591249 959084491452482089943437)
                ·
                  refine ⟨359656684294680783728789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959084491452482089943437 359656684294680783728789)
                  ·
                    rfl

theorem cell21_1575965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1575965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1575965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1575965 prefixEnd_1575965 := by exact prefixLift 1575965
  have htrace : WordTrace (prefixWord ++ tailWord_1575965) baseStart_1575965 baseEnd_1575965 := by
    simpa [prefixWord, tailWord_1575965, baseEnd_1575965] using wordTrace_append hprefix tailTrace_1575965
  have hstable : (prefixWord ++ tailWord_1575965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1575965).length < 2 ^ (prefixWord ++ tailWord_1575965).sum := by decide
  have hdescent : baseEnd_1575965 < baseStart_1575965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1575965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576021 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_1576021 : Nat := 118140960795 + 1576021 * 2 ^ 59
def prefixEnd_1576021 : Nat := 4983230072969 + 3 ^ 40 * 1576021 * 2
def baseEnd_1576021 : Nat := 359669464257637130795341

theorem tailTrace_1576021 : CollatzResearch.WordTrace tailWord_1576021 prefixEnd_1576021 359669464257637130795341 := by
  unfold tailWord_1576021
  simp only [CollatzResearch.WordTrace]
  refine ⟨57482208223352554802751917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38321472148901703201834611 57482208223352554802751917)
  ·
    refine ⟨21555828083757208051031969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57482208223352554802751917 21555828083757208051031969)
    ·
      refine ⟨16166871062817906038273977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21555828083757208051031969 16166871062817906038273977)
      ·
        refine ⟨12125153297113429528705483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16166871062817906038273977 12125153297113429528705483)
        ·
          refine ⟨18187729945670144293058225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125153297113429528705483 18187729945670144293058225)
          ·
            refine ⟨13640797459252608219793669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18187729945670144293058225 13640797459252608219793669)
            ·
              refine ⟨2557649523609864041211313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13640797459252608219793669 2557649523609864041211313)
              ·
                refine ⟨1918237142707398030908485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557649523609864041211313 1918237142707398030908485)
                ·
                  refine ⟨359669464257637130795341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918237142707398030908485 359669464257637130795341)
                  ·
                    rfl

theorem cell21_1576021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_1576021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576021 prefixEnd_1576021 := by exact prefixLift 1576021
  have htrace : WordTrace (prefixWord ++ tailWord_1576021) baseStart_1576021 baseEnd_1576021 := by
    simpa [prefixWord, tailWord_1576021, baseEnd_1576021] using wordTrace_append hprefix tailTrace_1576021
  have hstable : (prefixWord ++ tailWord_1576021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576021).length < 2 ^ (prefixWord ++ tailWord_1576021).sum := by decide
  have hdescent : baseEnd_1576021 < baseStart_1576021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576080 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 4]
def baseStart_1576080 : Nat := 118140960795 + 1576080 * 2 ^ 59
def prefixEnd_1576080 : Nat := 4983230072969 + 3 ^ 40 * 1576080 * 2
def baseEnd_1576080 : Nat := 359682928861466139311887

theorem tailTrace_1576080 : CollatzResearch.WordTrace tailWord_1576080 prefixEnd_1576080 359682928861466139311887 := by
  unfold tailWord_1576080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28742180065069403939574847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38322906753425871919433129 28742180065069403939574847)
  ·
    refine ⟨43113270097604105909362271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28742180065069403939574847 43113270097604105909362271)
    ·
      refine ⟨64669905146406158864043407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43113270097604105909362271 64669905146406158864043407)
      ·
        refine ⟨97004857719609238296065111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64669905146406158864043407 97004857719609238296065111)
        ·
          refine ⟨145507286579413857444097667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97004857719609238296065111 145507286579413857444097667)
          ·
            refine ⟨218260929869120786166146501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145507286579413857444097667 218260929869120786166146501)
            ·
              refine ⟨40923924350460147406152469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218260929869120786166146501 40923924350460147406152469)
              ·
                refine ⟨1918308953927819409663397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40923924350460147406152469 1918308953927819409663397)
                ·
                  refine ⟨359682928861466139311887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918308953927819409663397 359682928861466139311887)
                  ·
                    rfl

theorem cell21_1576080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_1576080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576080 prefixEnd_1576080 := by exact prefixLift 1576080
  have htrace : WordTrace (prefixWord ++ tailWord_1576080) baseStart_1576080 baseEnd_1576080 := by
    simpa [prefixWord, tailWord_1576080, baseEnd_1576080] using wordTrace_append hprefix tailTrace_1576080
  have hstable : (prefixWord ++ tailWord_1576080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576080).length < 2 ^ (prefixWord ++ tailWord_1576080).sum := by decide
  have hdescent : baseEnd_1576080 < baseStart_1576080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576111 : List Nat := [1, 1, 2, 1, 2, 3, 6, 5]
def baseStart_1576111 : Nat := 118140960795 + 1576111 * 2 ^ 59
def prefixEnd_1576111 : Nat := 4983230072969 + 3 ^ 40 * 1576111 * 2
def baseEnd_1576111 : Nat := 119896667827938991431719

theorem tailTrace_1576111 : CollatzResearch.WordTrace tailWord_1576111 prefixEnd_1576111 119896667827938991431719 := by
  unfold tailWord_1576111
  simp only [CollatzResearch.WordTrace]
  refine ⟨57485490793026500173528187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38323660528684333449018791 57485490793026500173528187)
  ·
    refine ⟨86228236189539750260292281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57485490793026500173528187 86228236189539750260292281)
    ·
      refine ⟨64671177142154812695219211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86228236189539750260292281 64671177142154812695219211)
      ·
        refine ⟨97006765713232219042828817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64671177142154812695219211 97006765713232219042828817)
        ·
          refine ⟨72755074284924164282121613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97006765713232219042828817 72755074284924164282121613)
          ·
            refine ⟨27283152856846561605795605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72755074284924164282121613 27283152856846561605795605)
            ·
              refine ⟨1278897790164682575271669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27283152856846561605795605 1278897790164682575271669)
              ·
                refine ⟨119896667827938991431719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1278897790164682575271669 119896667827938991431719)
                ·
                  rfl

theorem cell21_1576111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].length) (baseStart_1576111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576111 prefixEnd_1576111 := by exact prefixLift 1576111
  have htrace : WordTrace (prefixWord ++ tailWord_1576111) baseStart_1576111 baseEnd_1576111 := by
    simpa [prefixWord, tailWord_1576111, baseEnd_1576111] using wordTrace_append hprefix tailTrace_1576111
  have hstable : (prefixWord ++ tailWord_1576111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576111).length < 2 ^ (prefixWord ++ tailWord_1576111).sum := by decide
  have hdescent : baseEnd_1576111 < baseStart_1576111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576125 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1576125 : Nat := 118140960795 + 1576125 * 2 ^ 59
def prefixEnd_1576125 : Nat := 4983230072969 + 3 ^ 40 * 1576125 * 2
def baseEnd_1576125 : Nat := 359693198474556061061795

theorem tailTrace_1576125 : CollatzResearch.WordTrace tailWord_1576125 prefixEnd_1576125 359693198474556061061795 := by
  unfold tailWord_1576125
  simp only [CollatzResearch.WordTrace]
  refine ⟨57486001414975780564537829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38324000943317187043025219 57486001414975780564537829)
  ·
    refine ⟨10778625265307958855850843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57486001414975780564537829 10778625265307958855850843)
    ·
      refine ⟨16167937897961938283776265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778625265307958855850843 16167937897961938283776265)
      ·
        refine ⟨12125953423471453712832199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16167937897961938283776265 12125953423471453712832199)
        ·
          refine ⟨18188930135207180569248299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125953423471453712832199 18188930135207180569248299)
          ·
            refine ⟨27283395202810770853872449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18188930135207180569248299 27283395202810770853872449)
            ·
              refine ⟨20462546402108078140404337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27283395202810770853872449 20462546402108078140404337)
              ·
                refine ⟨15346909801581058605303253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20462546402108078140404337 15346909801581058605303253)
                ·
                  refine ⟨359693198474556061061795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15346909801581058605303253 359693198474556061061795)
                  ·
                    rfl

theorem cell21_1576125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1576125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576125 prefixEnd_1576125 := by exact prefixLift 1576125
  have htrace : WordTrace (prefixWord ++ tailWord_1576125) baseStart_1576125 baseEnd_1576125 := by
    simpa [prefixWord, tailWord_1576125, baseEnd_1576125] using wordTrace_append hprefix tailTrace_1576125
  have hstable : (prefixWord ++ tailWord_1576125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576125).length < 2 ^ (prefixWord ++ tailWord_1576125).sum := by decide
  have hdescent : baseEnd_1576125 < baseStart_1576125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576128 : List Nat := [2, 1, 1, 2, 7, 1, 7]
def baseStart_1576128 : Nat := 118140960795 + 1576128 * 2 ^ 59
def prefixEnd_1576128 : Nat := 4983230072969 + 3 ^ 40 * 1576128 * 2
def baseEnd_1576128 : Nat := 39965987012825413612421

theorem tailTrace_1576128 : CollatzResearch.WordTrace tailWord_1576128 prefixEnd_1576128 39965987012825413612421 := by
  unfold tailWord_1576128
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743055416982456038448519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38324073889309941384598025 28743055416982456038448519)
  ·
    refine ⟨43114583125473684057672779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28743055416982456038448519 43114583125473684057672779)
    ·
      refine ⟨64671874688210526086509169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43114583125473684057672779 64671874688210526086509169)
      ·
        refine ⟨48503906016157894564881877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64671874688210526086509169 48503906016157894564881877)
        ·
          refine ⟨1136810297253700653864419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48503906016157894564881877 1136810297253700653864419)
          ·
            refine ⟨1705215445880550980796629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136810297253700653864419 1705215445880550980796629)
            ·
              refine ⟨39965987012825413612421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1705215445880550980796629 39965987012825413612421)
              ·
                rfl

theorem cell21_1576128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 7].length) (baseStart_1576128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576128 prefixEnd_1576128 := by exact prefixLift 1576128
  have htrace : WordTrace (prefixWord ++ tailWord_1576128) baseStart_1576128 baseEnd_1576128 := by
    simpa [prefixWord, tailWord_1576128, baseEnd_1576128] using wordTrace_append hprefix tailTrace_1576128
  have hstable : (prefixWord ++ tailWord_1576128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576128).length < 2 ^ (prefixWord ++ tailWord_1576128).sum := by decide
  have hdescent : baseEnd_1576128 < baseStart_1576128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576134 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1576134 : Nat := 118140960795 + 1576134 * 2 ^ 59
def prefixEnd_1576134 : Nat := 4983230072969 + 3 ^ 40 * 1576134 * 2
def baseEnd_1576134 : Nat := 359695252397174045411777

theorem tailTrace_1576134 : CollatzResearch.WordTrace tailWord_1576134 prefixEnd_1576134 359695252397174045411777 := by
  unfold tailWord_1576134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796447802248224221925483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38324219781295450067743637 1796447802248224221925483)
  ·
    refine ⟨2694671703372336332888225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796447802248224221925483 2694671703372336332888225)
    ·
      refine ⟨2021003777529252249666169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694671703372336332888225 2021003777529252249666169)
      ·
        refine ⟨1515752833146939187249627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021003777529252249666169 1515752833146939187249627)
        ·
          refine ⟨2273629249720408780874441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515752833146939187249627 2273629249720408780874441)
          ·
            refine ⟨1705221937290306585655831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273629249720408780874441 1705221937290306585655831)
            ·
              refine ⟨2557832905935459878483747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705221937290306585655831 2557832905935459878483747)
              ·
                refine ⟨3836749358903189817725621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557832905935459878483747 3836749358903189817725621)
                ·
                  refine ⟨359695252397174045411777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836749358903189817725621 359695252397174045411777)
                  ·
                    rfl

theorem cell21_1576134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1576134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576134 prefixEnd_1576134 := by exact prefixLift 1576134
  have htrace : WordTrace (prefixWord ++ tailWord_1576134) baseStart_1576134 baseEnd_1576134 := by
    simpa [prefixWord, tailWord_1576134, baseEnd_1576134] using wordTrace_append hprefix tailTrace_1576134
  have hstable : (prefixWord ++ tailWord_1576134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576134).length < 2 ^ (prefixWord ++ tailWord_1576134).sum := by decide
  have hdescent : baseEnd_1576134 < baseStart_1576134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576148 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1576148 : Nat := 118140960795 + 1576148 * 2 ^ 59
def prefixEnd_1576148 : Nat := 4983230072969 + 3 ^ 40 * 1576148 * 2
def baseEnd_1576148 : Nat := 359698447387913132178415

theorem tailTrace_1576148 : CollatzResearch.WordTrace tailWord_1576148 prefixEnd_1576148 359698447387913132178415 := by
  unfold tailWord_1576148
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743420146946227746312549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38324560195928303661750065 28743420146946227746312549)
  ·
    refine ⟨5389391277552417702433603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28743420146946227746312549 5389391277552417702433603)
    ·
      refine ⟨8084086916328626553650405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389391277552417702433603 8084086916328626553650405)
      ·
        refine ⟨1515766296811617478809451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8084086916328626553650405 1515766296811617478809451)
        ·
          refine ⟨2273649445217426218214177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515766296811617478809451 2273649445217426218214177)
          ·
            refine ⟨1705237083913069663660633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273649445217426218214177 1705237083913069663660633)
            ·
              refine ⟨1278927812934802247745475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705237083913069663660633 1278927812934802247745475)
              ·
                refine ⟨1918391719402203371618213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278927812934802247745475 1918391719402203371618213)
                ·
                  refine ⟨359698447387913132178415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918391719402203371618213 359698447387913132178415)
                  ·
                    rfl

theorem cell21_1576148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1576148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576148 prefixEnd_1576148 := by exact prefixLift 1576148
  have htrace : WordTrace (prefixWord ++ tailWord_1576148) baseStart_1576148 baseEnd_1576148 := by
    simpa [prefixWord, tailWord_1576148, baseEnd_1576148] using wordTrace_append hprefix tailTrace_1576148
  have hstable : (prefixWord ++ tailWord_1576148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576148).length < 2 ^ (prefixWord ++ tailWord_1576148).sum := by decide
  have hdescent : baseEnd_1576148 < baseStart_1576148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576190 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1576190 : Nat := 118140960795 + 1576190 * 2 ^ 59
def prefixEnd_1576190 : Nat := 4983230072969 + 3 ^ 40 * 1576190 * 2
def baseEnd_1576190 : Nat := 359708032360130392478329

theorem tailTrace_1576190 : CollatzResearch.WordTrace tailWord_1576190 prefixEnd_1576190 359708032360130392478329 := by
  unfold tailWord_1576190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186046519967537083206753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38325581439826864443769349 7186046519967537083206753)
  ·
    refine ⟨5389534889975652812405065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186046519967537083206753 5389534889975652812405065)
    ·
      refine ⟨4042151167481739609303799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5389534889975652812405065 4042151167481739609303799)
      ·
        refine ⟨6063226751222609413955699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042151167481739609303799 6063226751222609413955699)
        ·
          refine ⟨9094840126833914120933549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6063226751222609413955699 9094840126833914120933549)
          ·
            refine ⟨3410565047562717795350081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9094840126833914120933549 3410565047562717795350081)
            ·
              refine ⟨2557923785672038346512561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410565047562717795350081 2557923785672038346512561)
              ·
                refine ⟨1918442839254028759884421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2557923785672038346512561 1918442839254028759884421)
                ·
                  refine ⟨359708032360130392478329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918442839254028759884421 359708032360130392478329)
                  ·
                    rfl

theorem cell21_1576190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1576190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576190 prefixEnd_1576190 := by exact prefixLift 1576190
  have htrace : WordTrace (prefixWord ++ tailWord_1576190) baseStart_1576190 baseEnd_1576190 := by
    simpa [prefixWord, tailWord_1576190, baseEnd_1576190] using wordTrace_append hprefix tailTrace_1576190
  have hstable : (prefixWord ++ tailWord_1576190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576190).length < 2 ^ (prefixWord ++ tailWord_1576190).sum := by decide
  have hdescent : baseEnd_1576190 < baseStart_1576190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576201 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_1576201 : Nat := 118140960795 + 1576201 * 2 ^ 59
def prefixEnd_1576201 : Nat := 4983230072969 + 3 ^ 40 * 1576201 * 2
def baseEnd_1576201 : Nat := 359710542709996817794973

theorem tailTrace_1576201 : CollatzResearch.WordTrace tailWord_1576201 prefixEnd_1576201 359710542709996817794973 := by
  unfold tailWord_1576201
  simp only [CollatzResearch.WordTrace]
  refine ⟨57488773362700445544304457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38325848908466963696202971 57488773362700445544304457)
  ·
    refine ⟨43116580022025334158228343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57488773362700445544304457 43116580022025334158228343)
    ·
      refine ⟨64674870033038001237342515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43116580022025334158228343 64674870033038001237342515)
      ·
        refine ⟨97012305049557001856013773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64674870033038001237342515 97012305049557001856013773)
        ·
          refine ⟨36379614393583875696005165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97012305049557001856013773 36379614393583875696005165)
          ·
            refine ⟨13642355397593953386001937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36379614393583875696005165 13642355397593953386001937)
            ·
              refine ⟨10231766548195465039501453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13642355397593953386001937 10231766548195465039501453)
              ·
                refine ⟨3836912455573299389813045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10231766548195465039501453 3836912455573299389813045)
                ·
                  refine ⟨359710542709996817794973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836912455573299389813045 359710542709996817794973)
                  ·
                    rfl

theorem cell21_1576201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_1576201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576201 prefixEnd_1576201 := by exact prefixLift 1576201
  have htrace : WordTrace (prefixWord ++ tailWord_1576201) baseStart_1576201 baseEnd_1576201 := by
    simpa [prefixWord, tailWord_1576201, baseEnd_1576201] using wordTrace_append hprefix tailTrace_1576201
  have hstable : (prefixWord ++ tailWord_1576201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576201).length < 2 ^ (prefixWord ++ tailWord_1576201).sum := by decide
  have hdescent : baseEnd_1576201 < baseStart_1576201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576218 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1576218 : Nat := 118140960795 + 1576218 * 2 ^ 59
def prefixEnd_1576218 : Nat := 4983230072969 + 3 ^ 40 * 1576218 * 2
def baseEnd_1576218 : Nat := 359714422341608566011605

theorem tailTrace_1576218 : CollatzResearch.WordTrace tailWord_1576218 prefixEnd_1576218 359714422341608566011605 := by
  unfold tailWord_1576218
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372348350909714361918327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38326262269092571631782205 14372348350909714361918327)
  ·
    refine ⟨21558522526364571542877491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14372348350909714361918327 21558522526364571542877491)
    ·
      refine ⟨32337783789546857314316237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21558522526364571542877491 32337783789546857314316237)
      ·
        refine ⟨12126668921080071492868589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32337783789546857314316237 12126668921080071492868589)
        ·
          refine ⟨4547500845405026809825721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12126668921080071492868589 4547500845405026809825721)
          ·
            refine ⟨3410625634053770107369291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547500845405026809825721 3410625634053770107369291)
            ·
              refine ⟨5115938451080655161053937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410625634053770107369291 5115938451080655161053937)
              ·
                refine ⟨3836953838310491370790453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115938451080655161053937 3836953838310491370790453)
                ·
                  refine ⟨359714422341608566011605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836953838310491370790453 359714422341608566011605)
                  ·
                    rfl

theorem cell21_1576218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1576218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576218 prefixEnd_1576218 := by exact prefixLift 1576218
  have htrace : WordTrace (prefixWord ++ tailWord_1576218) baseStart_1576218 baseEnd_1576218 := by
    simpa [prefixWord, tailWord_1576218, baseEnd_1576218] using wordTrace_append hprefix tailTrace_1576218
  have hstable : (prefixWord ++ tailWord_1576218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576218).length < 2 ^ (prefixWord ++ tailWord_1576218).sum := by decide
  have hdescent : baseEnd_1576218 < baseStart_1576218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576249 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_1576249 : Nat := 118140960795 + 1576249 * 2 ^ 59
def prefixEnd_1576249 : Nat := 4983230072969 + 3 ^ 40 * 1576249 * 2
def baseEnd_1576249 : Nat := 359721496963959400994875

theorem tailTrace_1576249 : CollatzResearch.WordTrace tailWord_1576249 prefixEnd_1576249 359721496963959400994875 := by
  unfold tailWord_1576249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57490524066526549742051801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38327016044351033161367867 57490524066526549742051801)
  ·
    refine ⟨43117893049894912306538851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57490524066526549742051801 43117893049894912306538851)
    ·
      refine ⟨64676839574842368459808277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43117893049894912306538851 64676839574842368459808277)
      ·
        refine ⟨3031726855070736021553513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64676839574842368459808277 3031726855070736021553513)
        ·
          refine ⟨2273795141303052016165135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031726855070736021553513 2273795141303052016165135)
          ·
            refine ⟨3410692711954578024247703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273795141303052016165135 3410692711954578024247703)
            ·
              refine ⟨5116039067931867036371555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410692711954578024247703 5116039067931867036371555)
              ·
                refine ⟨7674058601897800554557333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116039067931867036371555 7674058601897800554557333)
                ·
                  refine ⟨359721496963959400994875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7674058601897800554557333 359721496963959400994875)
                  ·
                    rfl

theorem cell21_1576249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_1576249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576249 prefixEnd_1576249 := by exact prefixLift 1576249
  have htrace : WordTrace (prefixWord ++ tailWord_1576249) baseStart_1576249 baseEnd_1576249 := by
    simpa [prefixWord, tailWord_1576249, baseEnd_1576249] using wordTrace_append hprefix tailTrace_1576249
  have hstable : (prefixWord ++ tailWord_1576249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576249).length < 2 ^ (prefixWord ++ tailWord_1576249).sum := by decide
  have hdescent : baseEnd_1576249 < baseStart_1576249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576311 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 3]
def baseStart_1576311 : Nat := 118140960795 + 1576311 * 2 ^ 59
def prefixEnd_1576311 : Nat := 4983230072969 + 3 ^ 40 * 1576311 * 2
def baseEnd_1576311 : Nat := 359735646208661070961415

theorem tailTrace_1576311 : CollatzResearch.WordTrace tailWord_1576311 prefixEnd_1576311 359735646208661070961415 := by
  unfold tailWord_1576311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57492785392301934330808787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38328523594867956220539191 57492785392301934330808787)
  ·
    refine ⟨86239178088452901496213181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57492785392301934330808787 86239178088452901496213181)
    ·
      refine ⟨32339691783169838061079943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86239178088452901496213181 32339691783169838061079943)
      ·
        refine ⟨48509537674754757091619915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32339691783169838061079943 48509537674754757091619915)
        ·
          refine ⟨72764306512132135637429873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48509537674754757091619915 72764306512132135637429873)
          ·
            refine ⟨54573229884099101728072405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72764306512132135637429873 54573229884099101728072405)
            ·
              refine ⟨1279060075408572696751697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54573229884099101728072405 1279060075408572696751697)
              ·
                refine ⟨959295056556429522563773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279060075408572696751697 959295056556429522563773)
                ·
                  refine ⟨359735646208661070961415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959295056556429522563773 359735646208661070961415)
                  ·
                    rfl

theorem cell21_1576311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].length) (baseStart_1576311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576311 prefixEnd_1576311 := by exact prefixLift 1576311
  have htrace : WordTrace (prefixWord ++ tailWord_1576311) baseStart_1576311 baseEnd_1576311 := by
    simpa [prefixWord, tailWord_1576311, baseEnd_1576311] using wordTrace_append hprefix tailTrace_1576311
  have hstable : (prefixWord ++ tailWord_1576311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576311).length < 2 ^ (prefixWord ++ tailWord_1576311).sum := by decide
  have hdescent : baseEnd_1576311 < baseStart_1576311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576325 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 4]
def baseStart_1576325 : Nat := 118140960795 + 1576325 * 2 ^ 59
def prefixEnd_1576325 : Nat := 4983230072969 + 3 ^ 40 * 1576325 * 2
def baseEnd_1576325 : Nat := 359738841199400157728053

theorem tailTrace_1576325 : CollatzResearch.WordTrace tailWord_1576325 prefixEnd_1576325 359738841199400157728053 := by
  unfold tailWord_1576325
  simp only [CollatzResearch.WordTrace]
  refine ⟨57493296014251214721818429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38328864009500809814545619 57493296014251214721818429)
  ·
    refine ⟨21559986005344205520681911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57493296014251214721818429 21559986005344205520681911)
    ·
      refine ⟨32339979008016308281022867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21559986005344205520681911 32339979008016308281022867)
      ·
        refine ⟨48509968512024462421534301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32339979008016308281022867 48509968512024462421534301)
        ·
          refine ⟨18191238192009173408075363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48509968512024462421534301 18191238192009173408075363)
          ·
            refine ⟨27286857288013760112113045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18191238192009173408075363 27286857288013760112113045)
            ·
              refine ⟨1279071435375645005255299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27286857288013760112113045 1279071435375645005255299)
              ·
                refine ⟨1918607153063467507882949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279071435375645005255299 1918607153063467507882949)
                ·
                  refine ⟨359738841199400157728053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918607153063467507882949 359738841199400157728053)
                  ·
                    rfl

theorem cell21_1576325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_1576325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576325 prefixEnd_1576325 := by exact prefixLift 1576325
  have htrace : WordTrace (prefixWord ++ tailWord_1576325) baseStart_1576325 baseEnd_1576325 := by
    simpa [prefixWord, tailWord_1576325, baseEnd_1576325] using wordTrace_append hprefix tailTrace_1576325
  have hstable : (prefixWord ++ tailWord_1576325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576325).length < 2 ^ (prefixWord ++ tailWord_1576325).sum := by decide
  have hdescent : baseEnd_1576325 < baseStart_1576325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576367 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_1576367 : Nat := 118140960795 + 1576367 * 2 ^ 59
def prefixEnd_1576367 : Nat := 4983230072969 + 3 ^ 40 * 1576367 * 2
def baseEnd_1576367 : Nat := 359748426171617418027967

theorem tailTrace_1576367 : CollatzResearch.WordTrace tailWord_1576367 prefixEnd_1576367 359748426171617418027967 := by
  unfold tailWord_1576367
  simp only [CollatzResearch.WordTrace]
  refine ⟨57494827880099055894847355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38329885253399370596564903 57494827880099055894847355)
  ·
    refine ⟨86242241820148583842271033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57494827880099055894847355 86242241820148583842271033)
    ·
      refine ⟨64681681365111437881703275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86242241820148583842271033 64681681365111437881703275)
      ·
        refine ⟨97022522047667156822554913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64681681365111437881703275 97022522047667156822554913)
        ·
          refine ⟨72766891535750367616916185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97022522047667156822554913 72766891535750367616916185)
          ·
            refine ⟨54575168651812775712687139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72766891535750367616916185 54575168651812775712687139)
            ·
              refine ⟨81862752977719163569030709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54575168651812775712687139 81862752977719163569030709)
              ·
                refine ⟨7674633091661171584596629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81862752977719163569030709 7674633091661171584596629)
                ·
                  refine ⟨359748426171617418027967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7674633091661171584596629 359748426171617418027967)
                  ·
                    rfl

theorem cell21_1576367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_1576367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576367 prefixEnd_1576367 := by exact prefixLift 1576367
  have htrace : WordTrace (prefixWord ++ tailWord_1576367) baseStart_1576367 baseEnd_1576367 := by
    simpa [prefixWord, tailWord_1576367, baseEnd_1576367] using wordTrace_append hprefix tailTrace_1576367
  have hstable : (prefixWord ++ tailWord_1576367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576367).length < 2 ^ (prefixWord ++ tailWord_1576367).sum := by decide
  have hdescent : baseEnd_1576367 < baseStart_1576367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576384 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_1576384 : Nat := 118140960795 + 1576384 * 2 ^ 59
def prefixEnd_1576384 : Nat := 4983230072969 + 3 ^ 40 * 1576384 * 2
def baseEnd_1576384 : Nat := 359752305803229166244599

theorem tailTrace_1576384 : CollatzResearch.WordTrace tailWord_1576384 prefixEnd_1576384 359752305803229166244599 := by
  unfold tailWord_1576384
  simp only [CollatzResearch.WordTrace]
  refine ⟨28747723960518733899108103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38330298614024978532144137 28747723960518733899108103)
  ·
    refine ⟨43121585940778100848662155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28747723960518733899108103 43121585940778100848662155)
    ·
      refine ⟨64682378911167151272993233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43121585940778100848662155 64682378911167151272993233)
      ·
        refine ⟨48511784183375363454744925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64682378911167151272993233 48511784183375363454744925)
        ·
          refine ⟨18191919068765761295529347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48511784183375363454744925 18191919068765761295529347)
          ·
            refine ⟨27287878603148641943294021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18191919068765761295529347 27287878603148641943294021)
            ·
              refine ⟨5116477238090370364367629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27287878603148641943294021 5116477238090370364367629)
              ·
                refine ⟨1918678964283888886637861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5116477238090370364367629 1918678964283888886637861)
                ·
                  refine ⟨359752305803229166244599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918678964283888886637861 359752305803229166244599)
                  ·
                    rfl

theorem cell21_1576384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_1576384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576384 prefixEnd_1576384 := by exact prefixLift 1576384
  have htrace : WordTrace (prefixWord ++ tailWord_1576384) baseStart_1576384 baseEnd_1576384 := by
    simpa [prefixWord, tailWord_1576384, baseEnd_1576384] using wordTrace_append hprefix tailTrace_1576384
  have hstable : (prefixWord ++ tailWord_1576384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576384).length < 2 ^ (prefixWord ++ tailWord_1576384).sum := by decide
  have hdescent : baseEnd_1576384 < baseStart_1576384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576398 : List Nat := [4, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1576398 : Nat := 118140960795 + 1576398 * 2 ^ 59
def prefixEnd_1576398 : Nat := 4983230072969 + 3 ^ 40 * 1576398 * 2
def baseEnd_1576398 : Nat := 119918500264656084337079

theorem tailTrace_1576398 : CollatzResearch.WordTrace tailWord_1576398 prefixEnd_1576398 119918500264656084337079 := by
  unfold tailWord_1576398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186994817873343523653231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38330639028657832126150565 7186994817873343523653231)
  ·
    refine ⟨10780492226810015285479847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7186994817873343523653231 10780492226810015285479847)
    ·
      refine ⟨16170738340215022928219771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10780492226810015285479847 16170738340215022928219771)
      ·
        refine ⟨24256107510322534392329657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16170738340215022928219771 24256107510322534392329657)
        ·
          refine ⟨18192080632741900794247243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24256107510322534392329657 18192080632741900794247243)
          ·
            refine ⟨27288120949112851191370865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18192080632741900794247243 27288120949112851191370865)
            ·
              refine ⟨20466090711834638393528149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27288120949112851191370865 20466090711834638393528149)
              ·
                refine ⟨119918500264656084337079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20466090711834638393528149 119918500264656084337079)
                ·
                  rfl

theorem cell21_1576398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1576398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576398 prefixEnd_1576398 := by exact prefixLift 1576398
  have htrace : WordTrace (prefixWord ++ tailWord_1576398) baseStart_1576398 baseEnd_1576398 := by
    simpa [prefixWord, tailWord_1576398, baseEnd_1576398] using wordTrace_append hprefix tailTrace_1576398
  have hstable : (prefixWord ++ tailWord_1576398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576398).length < 2 ^ (prefixWord ++ tailWord_1576398).sum := by decide
  have hdescent : baseEnd_1576398 < baseStart_1576398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576404 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1576404 : Nat := 118140960795 + 1576404 * 2 ^ 59
def prefixEnd_1576404 : Nat := 4983230072969 + 3 ^ 40 * 1576404 * 2
def baseEnd_1576404 : Nat := 359756870075713575911225

theorem tailTrace_1576404 : CollatzResearch.WordTrace tailWord_1576404 prefixEnd_1576404 359756870075713575911225 := by
  unfold tailWord_1576404
  simp only [CollatzResearch.WordTrace]
  refine ⟨28748088690482505606972133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38330784920643340809296177 28748088690482505606972133)
  ·
    refine ⟨5390266629465469801307275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28748088690482505606972133 5390266629465469801307275)
    ·
      refine ⟨8085399944198204701960913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390266629465469801307275 8085399944198204701960913)
      ·
        refine ⟨6064049958148653526470685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8085399944198204701960913 6064049958148653526470685)
        ·
          refine ⟨2274018734305745072426507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6064049958148653526470685 2274018734305745072426507)
          ·
            refine ⟨3411028101458617608639761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274018734305745072426507 3411028101458617608639761)
            ·
              refine ⟨2558271076093963206479821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411028101458617608639761 2558271076093963206479821)
              ·
                refine ⟨959351653535236202429933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558271076093963206479821 959351653535236202429933)
                ·
                  refine ⟨359756870075713575911225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959351653535236202429933 359756870075713575911225)
                  ·
                    rfl

theorem cell21_1576404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1576404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576404 prefixEnd_1576404 := by exact prefixLift 1576404
  have htrace : WordTrace (prefixWord ++ tailWord_1576404) baseStart_1576404 baseEnd_1576404 := by
    simpa [prefixWord, tailWord_1576404, baseEnd_1576404] using wordTrace_append hprefix tailTrace_1576404
  have hstable : (prefixWord ++ tailWord_1576404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576404).length < 2 ^ (prefixWord ++ tailWord_1576404).sum := by decide
  have hdescent : baseEnd_1576404 < baseStart_1576404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576449 : List Nat := [1, 2, 4, 1, 5, 1, 2, 5]
def baseStart_1576449 : Nat := 118140960795 + 1576449 * 2 ^ 59
def prefixEnd_1576449 : Nat := 4983230072969 + 3 ^ 40 * 1576449 * 2
def baseEnd_1576449 : Nat := 119922379896267832553711

theorem tailTrace_1576449 : CollatzResearch.WordTrace tailWord_1576449 prefixEnd_1576449 119922379896267832553711 := by
  unfold tailWord_1576449
  simp only [CollatzResearch.WordTrace]
  refine ⟨57497818665801983899332401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38331879110534655932888267 57497818665801983899332401)
  ·
    refine ⟨43123363999351487924499301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57497818665801983899332401 43123363999351487924499301)
    ·
      refine ⟨8085630749878403985843619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43123363999351487924499301 8085630749878403985843619)
      ·
        refine ⟨12128446124817605978765429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085630749878403985843619 12128446124817605978765429)
        ·
          refine ⟨1137041824201650560509259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12128446124817605978765429 1137041824201650560509259)
          ·
            refine ⟨1705562736302475840763889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137041824201650560509259 1705562736302475840763889)
            ·
              refine ⟨1279172052226856880572917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705562736302475840763889 1279172052226856880572917)
              ·
                refine ⟨119922379896267832553711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1279172052226856880572917 119922379896267832553711)
                ·
                  rfl

theorem cell21_1576449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 5].length) (baseStart_1576449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576449 prefixEnd_1576449 := by exact prefixLift 1576449
  have htrace : WordTrace (prefixWord ++ tailWord_1576449) baseStart_1576449 baseEnd_1576449 := by
    simpa [prefixWord, tailWord_1576449, baseEnd_1576449] using wordTrace_append hprefix tailTrace_1576449
  have hstable : (prefixWord ++ tailWord_1576449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576449).length < 2 ^ (prefixWord ++ tailWord_1576449).sum := by decide
  have hdescent : baseEnd_1576449 < baseStart_1576449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576480 : List Nat := [2, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_1576480 : Nat := 118140960795 + 1576480 * 2 ^ 59
def prefixEnd_1576480 : Nat := 4983230072969 + 3 ^ 40 * 1576480 * 2
def baseEnd_1576480 : Nat := 359774214311154332644403

theorem tailTrace_1576480 : CollatzResearch.WordTrace tailWord_1576480 prefixEnd_1576480 359774214311154332644403 := by
  unfold tailWord_1576480
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749474664344838096855447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38332632885793117462473929 28749474664344838096855447)
  ·
    refine ⟨43124211996517257145283171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28749474664344838096855447 43124211996517257145283171)
    ·
      refine ⟨64686317994775885717924757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43124211996517257145283171 64686317994775885717924757)
      ·
        refine ⟨3032171156005119643027723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64686317994775885717924757 3032171156005119643027723)
        ·
          refine ⟨4548256734007679464541585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032171156005119643027723 4548256734007679464541585)
          ·
            refine ⟨3411192550505759598406189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4548256734007679464541585 3411192550505759598406189)
            ·
              refine ⟨1279197206439659849402321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3411192550505759598406189 1279197206439659849402321)
              ·
                refine ⟨959397904829744887051741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279197206439659849402321 959397904829744887051741)
                ·
                  refine ⟨359774214311154332644403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959397904829744887051741 359774214311154332644403)
                  ·
                    rfl

theorem cell21_1576480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_1576480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576480 prefixEnd_1576480 := by exact prefixLift 1576480
  have htrace : WordTrace (prefixWord ++ tailWord_1576480) baseStart_1576480 baseEnd_1576480 := by
    simpa [prefixWord, tailWord_1576480, baseEnd_1576480] using wordTrace_append hprefix tailTrace_1576480
  have hstable : (prefixWord ++ tailWord_1576480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576480).length < 2 ^ (prefixWord ++ tailWord_1576480).sum := by decide
  have hdescent : baseEnd_1576480 < baseStart_1576480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576494 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1576494 : Nat := 118140960795 + 1576494 * 2 ^ 59
def prefixEnd_1576494 : Nat := 4983230072969 + 3 ^ 40 * 1576494 * 2
def baseEnd_1576494 : Nat := 359777409301893419411041

theorem tailTrace_1576494 : CollatzResearch.WordTrace tailWord_1576494 prefixEnd_1576494 359777409301893419411041 := by
  unfold tailWord_1576494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187432493829869573090067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38332973300425971056480357 7187432493829869573090067)
  ·
    refine ⟨10781148740744804359635101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187432493829869573090067 10781148740744804359635101)
    ·
      refine ⟨4042930777779301634863163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10781148740744804359635101 4042930777779301634863163)
      ·
        refine ⟨6064396166668952452294745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042930777779301634863163 6064396166668952452294745)
        ·
          refine ⟨4548297125001714339221059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064396166668952452294745 4548297125001714339221059)
          ·
            refine ⟨6822445687502571508831589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548297125001714339221059 6822445687502571508831589)
            ·
              refine ⟨1279208566406732157905923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6822445687502571508831589 1279208566406732157905923)
              ·
                refine ⟨1918812849610098236858885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279208566406732157905923 1918812849610098236858885)
                ·
                  refine ⟨359777409301893419411041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1918812849610098236858885 359777409301893419411041)
                  ·
                    rfl

theorem cell21_1576494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1576494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576494 prefixEnd_1576494 := by exact prefixLift 1576494
  have htrace : WordTrace (prefixWord ++ tailWord_1576494) baseStart_1576494 baseEnd_1576494 := by
    simpa [prefixWord, tailWord_1576494, baseEnd_1576494] using wordTrace_append hprefix tailTrace_1576494
  have hstable : (prefixWord ++ tailWord_1576494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576494).length < 2 ^ (prefixWord ++ tailWord_1576494).sum := by decide
  have hdescent : baseEnd_1576494 < baseStart_1576494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576522 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1576522 : Nat := 118140960795 + 1576522 * 2 ^ 59
def prefixEnd_1576522 : Nat := 4983230072969 + 3 ^ 40 * 1576522 * 2
def baseEnd_1576522 : Nat := 359783799283371592944317

theorem tailTrace_1576522 : CollatzResearch.WordTrace tailWord_1576522 prefixEnd_1576522 359783799283371592944317 := by
  unfold tailWord_1576522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14375120298634379341684955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38333654129691678244493213 14375120298634379341684955)
  ·
    refine ⟨21562680447951569012527433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14375120298634379341684955 21562680447951569012527433)
    ·
      refine ⟨16172010335963676759395575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21562680447951569012527433 16172010335963676759395575)
      ·
        refine ⟨24258015503945515139093363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16172010335963676759395575 24258015503945515139093363)
        ·
          refine ⟨36387023255918272708640045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24258015503945515139093363 36387023255918272708640045)
          ·
            refine ⟨13645133720969352265740017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36387023255918272708640045 13645133720969352265740017)
            ·
              refine ⟨10233850290727014199305013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13645133720969352265740017 10233850290727014199305013)
              ·
                refine ⟨959423464755657581184845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10233850290727014199305013 959423464755657581184845)
                ·
                  refine ⟨359783799283371592944317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959423464755657581184845 359783799283371592944317)
                  ·
                    rfl

theorem cell21_1576522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1576522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576522 prefixEnd_1576522 := by exact prefixLift 1576522
  have htrace : WordTrace (prefixWord ++ tailWord_1576522) baseStart_1576522 baseEnd_1576522 := by
    simpa [prefixWord, tailWord_1576522, baseEnd_1576522] using wordTrace_append hprefix tailTrace_1576522
  have hstable : (prefixWord ++ tailWord_1576522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576522).length < 2 ^ (prefixWord ++ tailWord_1576522).sum := by decide
  have hdescent : baseEnd_1576522 < baseStart_1576522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576646 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1576646 : Nat := 118140960795 + 1576646 * 2 ^ 59
def prefixEnd_1576646 : Nat := 4983230072969 + 3 ^ 40 * 1576646 * 2
def baseEnd_1576646 : Nat := 359812097772774932877397

theorem tailTrace_1576646 : CollatzResearch.WordTrace tailWord_1576646 prefixEnd_1576646 359812097772774932877397 := by
  unfold tailWord_1576646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797031370190258954507931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38336669230725524362835861 1797031370190258954507931)
  ·
    refine ⟨2695547055285388431761897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797031370190258954507931 2695547055285388431761897)
    ·
      refine ⟨2021660291464041323821423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2695547055285388431761897 2021660291464041323821423)
      ·
        refine ⟨3032490437196061985732135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021660291464041323821423 3032490437196061985732135)
        ·
          refine ⟨4548735655794092978598203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032490437196061985732135 4548735655794092978598203)
          ·
            refine ⟨6823103483691139467897305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548735655794092978598203 6823103483691139467897305)
            ·
              refine ⟨5117327612768354600922979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6823103483691139467897305 5117327612768354600922979)
              ·
                refine ⟨7675991419152531901384469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5117327612768354600922979 7675991419152531901384469)
                ·
                  refine ⟨359812097772774932877397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7675991419152531901384469 359812097772774932877397)
                  ·
                    rfl

theorem cell21_1576646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1576646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576646 prefixEnd_1576646 := by exact prefixLift 1576646
  have htrace : WordTrace (prefixWord ++ tailWord_1576646) baseStart_1576646 baseEnd_1576646 := by
    simpa [prefixWord, tailWord_1576646, baseEnd_1576646] using wordTrace_append hprefix tailTrace_1576646
  have hstable : (prefixWord ++ tailWord_1576646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576646).length < 2 ^ (prefixWord ++ tailWord_1576646).sum := by decide
  have hdescent : baseEnd_1576646 < baseStart_1576646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576657 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_1576657 : Nat := 118140960795 + 1576657 * 2 ^ 59
def prefixEnd_1576657 : Nat := 4983230072969 + 3 ^ 40 * 1576657 * 2
def baseEnd_1576657 : Nat := 359814608122641358194041

theorem tailTrace_1576657 : CollatzResearch.WordTrace tailWord_1576657 prefixEnd_1576657 359814608122641358194041 := by
  unfold tailWord_1576657
  simp only [CollatzResearch.WordTrace]
  refine ⟨57505405049048435422904225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38336936699365623615269483 57505405049048435422904225)
  ·
    refine ⟨43129053786786326567178169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57505405049048435422904225 43129053786786326567178169)
    ·
      refine ⟨32346790340089744925383627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43129053786786326567178169 32346790340089744925383627)
      ·
        refine ⟨48520185510134617388075441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32346790340089744925383627 48520185510134617388075441)
        ·
          refine ⟨36390139132600963041056581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48520185510134617388075441 36390139132600963041056581)
          ·
            refine ⟨6823151087362680570198109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36390139132600963041056581 6823151087362680570198109)
            ·
              refine ⟨2558681657761005213824291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6823151087362680570198109 2558681657761005213824291)
              ·
                refine ⟨3838022486641507820736437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558681657761005213824291 3838022486641507820736437)
                ·
                  refine ⟨359814608122641358194041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3838022486641507820736437 359814608122641358194041)
                  ·
                    rfl

theorem cell21_1576657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_1576657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576657 prefixEnd_1576657 := by exact prefixLift 1576657
  have htrace : WordTrace (prefixWord ++ tailWord_1576657) baseStart_1576657 baseEnd_1576657 := by
    simpa [prefixWord, tailWord_1576657, baseEnd_1576657] using wordTrace_append hprefix tailTrace_1576657
  have hstable : (prefixWord ++ tailWord_1576657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576657).length < 2 ^ (prefixWord ++ tailWord_1576657).sum := by decide
  have hdescent : baseEnd_1576657 < baseStart_1576657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576702 : List Nat := [4, 2, 2, 1, 12]
def baseStart_1576702 : Nat := 118140960795 + 1576702 * 2 ^ 59
def prefixEnd_1576702 : Nat := 4983230072969 + 3 ^ 40 * 1576702 * 2
def baseEnd_1576702 : Nat := 4442282441181867653629

theorem tailTrace_1576702 : CollatzResearch.WordTrace tailWord_1576702 prefixEnd_1576702 4442282441181867653629 := by
  unfold tailWord_1576702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188380791735676013536545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38338030889256938738861573 7188380791735676013536545)
  ·
    refine ⟨5391285593801757010152409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7188380791735676013536545 5391285593801757010152409)
    ·
      refine ⟨4043464195351317757614307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5391285593801757010152409 4043464195351317757614307)
      ·
        refine ⟨6065196293026976636421461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043464195351317757614307 6065196293026976636421461)
        ·
          refine ⟨4442282441181867653629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6065196293026976636421461 4442282441181867653629)
          ·
            rfl

theorem cell21_1576702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 12].length) (baseStart_1576702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576702 prefixEnd_1576702 := by exact prefixLift 1576702
  have htrace : WordTrace (prefixWord ++ tailWord_1576702) baseStart_1576702 baseEnd_1576702 := by
    simpa [prefixWord, tailWord_1576702, baseEnd_1576702] using wordTrace_append hprefix tailTrace_1576702
  have hstable : (prefixWord ++ tailWord_1576702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576702).length < 2 ^ (prefixWord ++ tailWord_1576702).sum := by decide
  have hdescent : baseEnd_1576702 < baseStart_1576702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576708 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_1576708 : Nat := 118140960795 + 1576708 * 2 ^ 59
def prefixEnd_1576708 : Nat := 4983230072969 + 3 ^ 40 * 1576708 * 2
def baseEnd_1576708 : Nat := 359826247017476602843937

theorem tailTrace_1576708 : CollatzResearch.WordTrace tailWord_1576708 prefixEnd_1576708 359826247017476602843937 := by
  unfold tailWord_1576708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28753632585931835566505389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38338176781242447422007185 28753632585931835566505389)
  ·
    refine ⟨10782612219724438337439521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28753632585931835566505389 10782612219724438337439521)
    ·
      refine ⟨8086959164793328753079641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10782612219724438337439521 8086959164793328753079641)
      ·
        refine ⟨6065219373594996564809731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8086959164793328753079641 6065219373594996564809731)
        ·
          refine ⟨9097829060392494847214597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6065219373594996564809731 9097829060392494847214597)
          ·
            refine ⟨1705842948823592783852737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9097829060392494847214597 1705842948823592783852737)
            ·
              refine ⟨1279382211617694587889553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705842948823592783852737 1279382211617694587889553)
              ·
                refine ⟨959536658713270940917165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279382211617694587889553 959536658713270940917165)
                ·
                  refine ⟨359826247017476602843937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959536658713270940917165 359826247017476602843937)
                  ·
                    rfl

theorem cell21_1576708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_1576708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576708 prefixEnd_1576708 := by exact prefixLift 1576708
  have htrace : WordTrace (prefixWord ++ tailWord_1576708) baseStart_1576708 baseEnd_1576708 := by
    simpa [prefixWord, tailWord_1576708, baseEnd_1576708] using wordTrace_append hprefix tailTrace_1576708
  have hstable : (prefixWord ++ tailWord_1576708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576708).length < 2 ^ (prefixWord ++ tailWord_1576708).sum := by decide
  have hdescent : baseEnd_1576708 < baseStart_1576708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576764 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1576764 : Nat := 118140960795 + 1576764 * 2 ^ 59
def prefixEnd_1576764 : Nat := 4983230072969 + 3 ^ 40 * 1576764 * 2
def baseEnd_1576764 : Nat := 359839026980432949910489

theorem tailTrace_1576764 : CollatzResearch.WordTrace tailWord_1576764 prefixEnd_1576764 359839026980432949910489 := by
  unfold tailWord_1576764
  simp only [CollatzResearch.WordTrace]
  refine ⟨28754653829830396348524673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38339538439773861798032897 28754653829830396348524673)
  ·
    refine ⟨21565990372372797261393505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28754653829830396348524673 21565990372372797261393505)
    ·
      refine ⟨16174492779279597946045129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565990372372797261393505 16174492779279597946045129)
      ·
        refine ⟨12130869584459698459533847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16174492779279597946045129 12130869584459698459533847)
        ·
          refine ⟨18196304376689547689300771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12130869584459698459533847 18196304376689547689300771)
          ·
            refine ⟨27294456565034321533951157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18196304376689547689300771 27294456565034321533951157)
            ·
              refine ⟨2558855302971967643807921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27294456565034321533951157 2558855302971967643807921)
              ·
                refine ⟨1919141477228975732855941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558855302971967643807921 1919141477228975732855941)
                ·
                  refine ⟨359839026980432949910489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919141477228975732855941 359839026980432949910489)
                  ·
                    rfl

theorem cell21_1576764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1576764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576764 prefixEnd_1576764 := by exact prefixLift 1576764
  have htrace : WordTrace (prefixWord ++ tailWord_1576764) baseStart_1576764 baseEnd_1576764 := by
    simpa [prefixWord, tailWord_1576764, baseEnd_1576764] using wordTrace_append hprefix tailTrace_1576764
  have hstable : (prefixWord ++ tailWord_1576764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576764).length < 2 ^ (prefixWord ++ tailWord_1576764).sum := by decide
  have hdescent : baseEnd_1576764 < baseStart_1576764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576944 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_1576944 : Nat := 118140960795 + 1576944 * 2 ^ 59
def prefixEnd_1576944 : Nat := 4983230072969 + 3 ^ 40 * 1576944 * 2
def baseEnd_1576944 : Nat := 359880105432792636910121

theorem tailTrace_1576944 : CollatzResearch.WordTrace tailWord_1576944 prefixEnd_1576944 359880105432792636910121 := by
  unfold tailWord_1576944
  simp only [CollatzResearch.WordTrace]
  refine ⟨28757936399504341719300943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38343915199339122292401257 28757936399504341719300943)
  ·
    refine ⟨43136904599256512578951415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28757936399504341719300943 43136904599256512578951415)
    ·
      refine ⟨64705356898884768868427123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43136904599256512578951415 64705356898884768868427123)
      ·
        refine ⟨97058035348327153302640685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64705356898884768868427123 97058035348327153302640685)
        ·
          refine ⟨36396763255622682488490257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97058035348327153302640685 36396763255622682488490257)
          ·
            refine ⟨27297572441717011866367693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36396763255622682488490257 27297572441717011866367693)
            ·
              refine ⟨10236589665643879449887885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27297572441717011866367693 10236589665643879449887885)
              ·
                refine ⟨3838721124616454793707957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10236589665643879449887885 3838721124616454793707957)
                ·
                  refine ⟨359880105432792636910121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3838721124616454793707957 359880105432792636910121)
                  ·
                    rfl

theorem cell21_1576944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_1576944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576944 prefixEnd_1576944 := by exact prefixLift 1576944
  have htrace : WordTrace (prefixWord ++ tailWord_1576944) baseStart_1576944 baseEnd_1576944 := by
    simpa [prefixWord, tailWord_1576944, baseEnd_1576944] using wordTrace_append hprefix tailTrace_1576944
  have hstable : (prefixWord ++ tailWord_1576944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576944).length < 2 ^ (prefixWord ++ tailWord_1576944).sum := by decide
  have hdescent : baseEnd_1576944 < baseStart_1576944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1576950 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1576950 : Nat := 118140960795 + 1576950 * 2 ^ 59
def prefixEnd_1576950 : Nat := 4983230072969 + 3 ^ 40 * 1576950 * 2
def baseEnd_1576950 : Nat := 359881474714537959810109

theorem tailTrace_1576950 : CollatzResearch.WordTrace tailWord_1576950 prefixEnd_1576950 359881474714537959810109 := by
  unfold tailWord_1576950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594755727311684153957519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38344061091324630975546869 3594755727311684153957519)
  ·
    refine ⟨5392133590967526230936279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3594755727311684153957519 5392133590967526230936279)
    ·
      refine ⟨8088200386451289346404419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392133590967526230936279 8088200386451289346404419)
      ·
        refine ⟨12132300579676934019606629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8088200386451289346404419 12132300579676934019606629)
        ·
          refine ⟨2274806358689425128676243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12132300579676934019606629 2274806358689425128676243)
          ·
            refine ⟨3412209538034137693014365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274806358689425128676243 3412209538034137693014365)
            ·
              refine ⟨1279578576762801634880387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3412209538034137693014365 1279578576762801634880387)
              ·
                refine ⟨1919367865144202452320581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279578576762801634880387 1919367865144202452320581)
                ·
                  refine ⟨359881474714537959810109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919367865144202452320581 359881474714537959810109)
                  ·
                    rfl

theorem cell21_1576950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1576950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1576950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1576950 prefixEnd_1576950 := by exact prefixLift 1576950
  have htrace : WordTrace (prefixWord ++ tailWord_1576950) baseStart_1576950 baseEnd_1576950 := by
    simpa [prefixWord, tailWord_1576950, baseEnd_1576950] using wordTrace_append hprefix tailTrace_1576950
  have hstable : (prefixWord ++ tailWord_1576950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1576950).length < 2 ^ (prefixWord ++ tailWord_1576950).sum := by decide
  have hdescent : baseEnd_1576950 < baseStart_1576950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1576950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577006 : List Nat := [4, 1, 3, 1, 1, 2, 1, 8]
def baseStart_1577006 : Nat := 118140960795 + 1577006 * 2 ^ 59
def prefixEnd_1577006 : Nat := 4983230072969 + 3 ^ 40 * 1577006 * 2
def baseEnd_1577006 : Nat := 119964751559164768958887

theorem tailTrace_1577006 : CollatzResearch.WordTrace tailWord_1577006 prefixEnd_1577006 119964751559164768958887 := by
  unfold tailWord_1577006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7189766765598008503419859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38345422749856045351572581 7189766765598008503419859)
  ·
    refine ⟨10784650148397012755129789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7189766765598008503419859 10784650148397012755129789)
    ·
      refine ⟨4044243805648879783173671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10784650148397012755129789 4044243805648879783173671)
      ·
        refine ⟨6066365708473319674760507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044243805648879783173671 6066365708473319674760507)
        ·
          refine ⟨9099548562709979512140761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066365708473319674760507 9099548562709979512140761)
          ·
            refine ⟨6824661422032484634105571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9099548562709979512140761 6824661422032484634105571)
            ·
              refine ⟨10236992133048726951158357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6824661422032484634105571 10236992133048726951158357)
              ·
                refine ⟨119964751559164768958887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10236992133048726951158357 119964751559164768958887)
                ·
                  rfl

theorem cell21_1577006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_1577006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577006 prefixEnd_1577006 := by exact prefixLift 1577006
  have htrace : WordTrace (prefixWord ++ tailWord_1577006) baseStart_1577006 baseEnd_1577006 := by
    simpa [prefixWord, tailWord_1577006, baseEnd_1577006] using wordTrace_append hprefix tailTrace_1577006
  have hstable : (prefixWord ++ tailWord_1577006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577006).length < 2 ^ (prefixWord ++ tailWord_1577006).sum := by decide
  have hdescent : baseEnd_1577006 < baseStart_1577006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577009 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 4]
def baseStart_1577009 : Nat := 118140960795 + 1577009 * 2 ^ 59
def prefixEnd_1577009 : Nat := 4983230072969 + 3 ^ 40 * 1577009 * 2
def baseEnd_1577009 : Nat := 359894939318366968326655

theorem tailTrace_1577009 : CollatzResearch.WordTrace tailWord_1577009 prefixEnd_1577009 359894939318366968326655 := by
  unfold tailWord_1577009
  simp only [CollatzResearch.WordTrace]
  refine ⟨57518243543773199539718081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38345495695848799693145387 57518243543773199539718081)
  ·
    refine ⟨43138682657829899654788561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57518243543773199539718081 43138682657829899654788561)
    ·
      refine ⟨32354011993372424741091421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43138682657829899654788561 32354011993372424741091421)
      ·
        refine ⟨12132754497514659277909283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32354011993372424741091421 12132754497514659277909283)
        ·
          refine ⟨18199131746271988916863925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12132754497514659277909283 18199131746271988916863925)
          ·
            refine ⟨1706168601212998960955993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18199131746271988916863925 1706168601212998960955993)
            ·
              refine ⟨1279626450909749220716995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706168601212998960955993 1279626450909749220716995)
              ·
                refine ⟨1919439676364623831075493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279626450909749220716995 1919439676364623831075493)
                ·
                  refine ⟨359894939318366968326655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919439676364623831075493 359894939318366968326655)
                  ·
                    rfl

theorem cell21_1577009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_1577009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577009 prefixEnd_1577009 := by exact prefixLift 1577009
  have htrace : WordTrace (prefixWord ++ tailWord_1577009) baseStart_1577009 baseEnd_1577009 := by
    simpa [prefixWord, tailWord_1577009, baseEnd_1577009] using wordTrace_append hprefix tailTrace_1577009
  have hstable : (prefixWord ++ tailWord_1577009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577009).length < 2 ^ (prefixWord ++ tailWord_1577009).sum := by decide
  have hdescent : baseEnd_1577009 < baseStart_1577009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577020 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_1577020 : Nat := 118140960795 + 1577020 * 2 ^ 59
def prefixEnd_1577020 : Nat := 4983230072969 + 3 ^ 40 * 1577020 * 2
def baseEnd_1577020 : Nat := 359897449668233393643299

theorem tailTrace_1577020 : CollatzResearch.WordTrace tailWord_1577020 prefixEnd_1577020 359897449668233393643299 := by
  unfold tailWord_1577020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759322373366674209184257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38345763164488898945579009 28759322373366674209184257)
  ·
    refine ⟨21569491780025005656888193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28759322373366674209184257 21569491780025005656888193)
    ·
      refine ⟨16177118835018754242666145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21569491780025005656888193 16177118835018754242666145)
      ·
        refine ⟨12132839126264065681999609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177118835018754242666145 12132839126264065681999609)
        ·
          refine ⟨9099629344698049261499707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12132839126264065681999609 9099629344698049261499707)
          ·
            refine ⟨13649444017047073892249561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9099629344698049261499707 13649444017047073892249561)
            ·
              refine ⟨10237083012785305419187171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13649444017047073892249561 10237083012785305419187171)
              ·
                refine ⟨15355624519177958128780757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10237083012785305419187171 15355624519177958128780757)
                ·
                  refine ⟨359897449668233393643299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15355624519177958128780757 359897449668233393643299)
                  ·
                    rfl

theorem cell21_1577020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_1577020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577020 prefixEnd_1577020 := by exact prefixLift 1577020
  have htrace : WordTrace (prefixWord ++ tailWord_1577020) baseStart_1577020 baseEnd_1577020 := by
    simpa [prefixWord, tailWord_1577020, baseEnd_1577020] using wordTrace_append hprefix tailTrace_1577020
  have hstable : (prefixWord ++ tailWord_1577020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577020).length < 2 ^ (prefixWord ++ tailWord_1577020).sum := by decide
  have hdescent : baseEnd_1577020 < baseStart_1577020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577102 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_1577102 : Nat := 118140960795 + 1577102 * 2 ^ 59
def prefixEnd_1577102 : Nat := 4983230072969 + 3 ^ 40 * 1577102 * 2
def baseEnd_1577102 : Nat := 359916163185419473276465

theorem tailTrace_1577102 : CollatzResearch.WordTrace tailWord_1577102 prefixEnd_1577102 359916163185419473276465 := by
  unfold tailWord_1577102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190204441554534552856695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38347757021624184281902373 7190204441554534552856695)
  ·
    refine ⟨10785306662331801829285043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7190204441554534552856695 10785306662331801829285043)
    ·
      refine ⟨16177959993497702743927565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785306662331801829285043 16177959993497702743927565)
      ·
        refine ⟨6066734997561638528972837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16177959993497702743927565 6066734997561638528972837)
        ·
          refine ⟨1137512812042807224182407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6066734997561638528972837 1137512812042807224182407)
          ·
            refine ⟨1706269218064210836273611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137512812042807224182407 1706269218064210836273611)
            ·
              refine ⟨2559403827096316254410417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706269218064210836273611 2559403827096316254410417)
              ·
                refine ⟨1919552870322237190807813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559403827096316254410417 1919552870322237190807813)
                ·
                  refine ⟨359916163185419473276465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919552870322237190807813 359916163185419473276465)
                  ·
                    rfl

theorem cell21_1577102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_1577102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577102 prefixEnd_1577102 := by exact prefixLift 1577102
  have htrace : WordTrace (prefixWord ++ tailWord_1577102) baseStart_1577102 baseEnd_1577102 := by
    simpa [prefixWord, tailWord_1577102, baseEnd_1577102] using wordTrace_append hprefix tailTrace_1577102
  have hstable : (prefixWord ++ tailWord_1577102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577102).length < 2 ^ (prefixWord ++ tailWord_1577102).sum := by decide
  have hdescent : baseEnd_1577102 < baseStart_1577102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577164 : List Nat := [2, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_1577164 : Nat := 118140960795 + 1577164 * 2 ^ 59
def prefixEnd_1577164 : Nat := 4983230072969 + 3 ^ 40 * 1577164 * 2
def baseEnd_1577164 : Nat := 359930312430121143243005

theorem tailTrace_1577164 : CollatzResearch.WordTrace tailWord_1577164 prefixEnd_1577164 359930312430121143243005 := by
  unfold tailWord_1577164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761948429105830505805273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38349264572141107341073697 28761948429105830505805273)
  ·
    refine ⟨21571461321829372879353955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28761948429105830505805273 21571461321829372879353955)
    ·
      refine ⟨32357191982744059319030933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21571461321829372879353955 32357191982744059319030933)
      ·
        refine ⟨1516743374191127780579575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32357191982744059319030933 1516743374191127780579575)
        ·
          refine ⟨2275115061286691670869363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516743374191127780579575 2275115061286691670869363)
          ·
            refine ⟨3412672591930037506304045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275115061286691670869363 3412672591930037506304045)
            ·
              refine ⟨1279752221973764064864017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3412672591930037506304045 1279752221973764064864017)
              ·
                refine ⟨959814166480323048648013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279752221973764064864017 959814166480323048648013)
                ·
                  refine ⟨359930312430121143243005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959814166480323048648013 359930312430121143243005)
                  ·
                    rfl

theorem cell21_1577164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_1577164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577164 prefixEnd_1577164 := by exact prefixLift 1577164
  have htrace : WordTrace (prefixWord ++ tailWord_1577164) baseStart_1577164 baseEnd_1577164 := by
    simpa [prefixWord, tailWord_1577164, baseEnd_1577164] using wordTrace_append hprefix tailTrace_1577164
  have hstable : (prefixWord ++ tailWord_1577164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577164).length < 2 ^ (prefixWord ++ tailWord_1577164).sum := by decide
  have hdescent : baseEnd_1577164 < baseStart_1577164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577223 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 3]
def baseStart_1577223 : Nat := 118140960795 + 1577223 * 2 ^ 59
def prefixEnd_1577223 : Nat := 4983230072969 + 3 ^ 40 * 1577223 * 2
def baseEnd_1577223 : Nat := 359943777033950151759551

theorem tailTrace_1577223 : CollatzResearch.WordTrace tailWord_1577223 prefixEnd_1577223 359943777033950151759551 := by
  unfold tailWord_1577223
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526048764997914088008323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38350699176665276058672215 57526048764997914088008323)
  ·
    refine ⟨86289073147496871132012485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526048764997914088008323 86289073147496871132012485)
    ·
      refine ⟨16179201215155663337252341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86289073147496871132012485 16179201215155663337252341)
      ·
        refine ⟨1516800113920843437867407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16179201215155663337252341 1516800113920843437867407)
        ·
          refine ⟨2275200170881265156801111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516800113920843437867407 2275200170881265156801111)
          ·
            refine ⟨3412800256321897735201667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275200170881265156801111 3412800256321897735201667)
            ·
              refine ⟨5119200384482846602802501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412800256321897735201667 5119200384482846602802501)
              ·
                refine ⟨959850072090533738025469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5119200384482846602802501 959850072090533738025469)
                ·
                  refine ⟨359943777033950151759551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 959850072090533738025469 359943777033950151759551)
                  ·
                    rfl

theorem cell21_1577223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 3].length) (baseStart_1577223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577223 prefixEnd_1577223 := by exact prefixLift 1577223
  have htrace : WordTrace (prefixWord ++ tailWord_1577223) baseStart_1577223 baseEnd_1577223 := by
    simpa [prefixWord, tailWord_1577223, baseEnd_1577223] using wordTrace_append hprefix tailTrace_1577223
  have hstable : (prefixWord ++ tailWord_1577223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577223).length < 2 ^ (prefixWord ++ tailWord_1577223).sum := by decide
  have hdescent : baseEnd_1577223 < baseStart_1577223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577231 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_1577231 : Nat := 118140960795 + 1577231 * 2 ^ 59
def prefixEnd_1577231 : Nat := 4983230072969 + 3 ^ 40 * 1577231 * 2
def baseEnd_1577231 : Nat := 359945602742943915626201

theorem tailTrace_1577231 : CollatzResearch.WordTrace tailWord_1577231 prefixEnd_1577231 359945602742943915626201 := by
  unfold tailWord_1577231
  simp only [CollatzResearch.WordTrace]
  refine ⟨57526340548968931454299547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38350893699312620969533031 57526340548968931454299547)
  ·
    refine ⟨86289510823453397181449321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57526340548968931454299547 86289510823453397181449321)
    ·
      refine ⟨64717133117590047886086991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86289510823453397181449321 64717133117590047886086991)
      ·
        refine ⟨97075699676385071829130487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64717133117590047886086991 97075699676385071829130487)
        ·
          refine ⟨145613549514577607743695731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97075699676385071829130487 145613549514577607743695731)
          ·
            refine ⟨218420324271866411615543597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145613549514577607743695731 218420324271866411615543597)
            ·
              refine ⟨81907621601949904355828849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218420324271866411615543597 81907621601949904355828849)
              ·
                refine ⟨61430716201462428266871637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81907621601949904355828849 61430716201462428266871637)
                ·
                  refine ⟨359945602742943915626201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61430716201462428266871637 359945602742943915626201)
                  ·
                    rfl

theorem cell21_1577231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_1577231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577231 prefixEnd_1577231 := by exact prefixLift 1577231
  have htrace : WordTrace (prefixWord ++ tailWord_1577231) baseStart_1577231 baseEnd_1577231 := by
    simpa [prefixWord, tailWord_1577231, baseEnd_1577231] using wordTrace_append hprefix tailTrace_1577231
  have hstable : (prefixWord ++ tailWord_1577231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577231).length < 2 ^ (prefixWord ++ tailWord_1577231).sum := by decide
  have hdescent : baseEnd_1577231 < baseStart_1577231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577248 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_1577248 : Nat := 118140960795 + 1577248 * 2 ^ 59
def prefixEnd_1577248 : Nat := 4983230072969 + 3 ^ 40 * 1577248 * 2
def baseEnd_1577248 : Nat := 359949482374555663842833

theorem tailTrace_1577248 : CollatzResearch.WordTrace tailWord_1577248 prefixEnd_1577248 359949482374555663842833 := by
  unfold tailWord_1577248
  simp only [CollatzResearch.WordTrace]
  refine ⟨28763480294953671678834199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38351307059938228905112265 28763480294953671678834199)
  ·
    refine ⟨43145220442430507518251299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28763480294953671678834199 43145220442430507518251299)
    ·
      refine ⟨64717830663645761277376949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43145220442430507518251299 64717830663645761277376949)
      ·
        refine ⟨6067296624716790119754089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64717830663645761277376949 6067296624716790119754089)
        ·
          refine ⟨4550472468537592589815567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6067296624716790119754089 4550472468537592589815567)
          ·
            refine ⟨6825708702806388884723351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550472468537592589815567 6825708702806388884723351)
            ·
              refine ⟨10238563054209583327085027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825708702806388884723351 10238563054209583327085027)
              ·
                refine ⟨15357844581314374990627541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10238563054209583327085027 15357844581314374990627541)
                ·
                  refine ⟨359949482374555663842833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15357844581314374990627541 359949482374555663842833)
                  ·
                    rfl

theorem cell21_1577248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_1577248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577248 prefixEnd_1577248 := by exact prefixLift 1577248
  have htrace : WordTrace (prefixWord ++ tailWord_1577248) baseStart_1577248 baseEnd_1577248 := by
    simpa [prefixWord, tailWord_1577248, baseEnd_1577248] using wordTrace_append hprefix tailTrace_1577248
  have hstable : (prefixWord ++ tailWord_1577248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577248).length < 2 ^ (prefixWord ++ tailWord_1577248).sum := by decide
  have hdescent : baseEnd_1577248 < baseStart_1577248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577296 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_1577296 : Nat := 118140960795 + 1577296 * 2 ^ 59
def prefixEnd_1577296 : Nat := 4983230072969 + 3 ^ 40 * 1577296 * 2
def baseEnd_1577296 : Nat := 359960436628518247042735

theorem tailTrace_1577296 : CollatzResearch.WordTrace tailWord_1577296 prefixEnd_1577296 359960436628518247042735 := by
  unfold tailWord_1577296
  simp only [CollatzResearch.WordTrace]
  refine ⟨28764355646866723777707871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38352474195822298370277161 28764355646866723777707871)
  ·
    refine ⟨43146533470300085666561807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28764355646866723777707871 43146533470300085666561807)
    ·
      refine ⟨64719800205450128499842711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43146533470300085666561807 64719800205450128499842711)
      ·
        refine ⟨97079700308175192749764067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64719800205450128499842711 97079700308175192749764067)
        ·
          refine ⟨145619550462262789124646101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97079700308175192749764067 145619550462262789124646101)
          ·
            refine ⟨3412958213959284120108893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 145619550462262789124646101 3412958213959284120108893)
            ·
              refine ⟨1279859330234731545040835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3412958213959284120108893 1279859330234731545040835)
              ·
                refine ⟨1919788995352097317561253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279859330234731545040835 1919788995352097317561253)
                ·
                  refine ⟨359960436628518247042735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919788995352097317561253 359960436628518247042735)
                  ·
                    rfl

theorem cell21_1577296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_1577296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577296 prefixEnd_1577296 := by exact prefixLift 1577296
  have htrace : WordTrace (prefixWord ++ tailWord_1577296) baseStart_1577296 baseEnd_1577296 := by
    simpa [prefixWord, tailWord_1577296, baseEnd_1577296] using wordTrace_append hprefix tailTrace_1577296
  have hstable : (prefixWord ++ tailWord_1577296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577296).length < 2 ^ (prefixWord ++ tailWord_1577296).sum := by decide
  have hdescent : baseEnd_1577296 < baseStart_1577296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577341 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1577341 : Nat := 118140960795 + 1577341 * 2 ^ 59
def prefixEnd_1577341 : Nat := 4983230072969 + 3 ^ 40 * 1577341 * 2
def baseEnd_1577341 : Nat := 359970706241608168792643

theorem tailTrace_1577341 : CollatzResearch.WordTrace tailWord_1577341 prefixEnd_1577341 359970706241608168792643 := by
  unfold tailWord_1577341
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530352578570420240803877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38353568385713613493869251 57530352578570420240803877)
  ·
    refine ⟨10786941108481953795150727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57530352578570420240803877 10786941108481953795150727)
    ·
      refine ⟨16180411662722930692726091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786941108481953795150727 16180411662722930692726091)
      ·
        refine ⟨24270617494084396039089137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180411662722930692726091 24270617494084396039089137)
        ·
          refine ⟨18202963120563297029316853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24270617494084396039089137 18202963120563297029316853)
          ·
            refine ⟨1706527792552809096498455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18202963120563297029316853 1706527792552809096498455)
            ·
              refine ⟨2559791688829213644747683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706527792552809096498455 2559791688829213644747683)
              ·
                refine ⟨3839687533243820467121525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559791688829213644747683 3839687533243820467121525)
                ·
                  refine ⟨359970706241608168792643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3839687533243820467121525 359970706241608168792643)
                  ·
                    rfl

theorem cell21_1577341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1577341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577341 prefixEnd_1577341 := by exact prefixLift 1577341
  have htrace : WordTrace (prefixWord ++ tailWord_1577341) baseStart_1577341 baseEnd_1577341 := by
    simpa [prefixWord, tailWord_1577341, baseEnd_1577341] using wordTrace_append hprefix tailTrace_1577341
  have hstable : (prefixWord ++ tailWord_1577341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577341).length < 2 ^ (prefixWord ++ tailWord_1577341).sum := by decide
  have hdescent : baseEnd_1577341 < baseStart_1577341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577355 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_1577355 : Nat := 118140960795 + 1577355 * 2 ^ 59
def prefixEnd_1577355 : Nat := 4983230072969 + 3 ^ 40 * 1577355 * 2
def baseEnd_1577355 : Nat := 359973901232347255559281

theorem tailTrace_1577355 : CollatzResearch.WordTrace tailWord_1577355 prefixEnd_1577355 359973901232347255559281 := by
  unfold tailWord_1577355
  simp only [CollatzResearch.WordTrace]
  refine ⟨57530863200519700631813519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38353908800346467087875679 57530863200519700631813519)
  ·
    refine ⟨86296294800779550947720279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57530863200519700631813519 86296294800779550947720279)
    ·
      refine ⟨129444442201169326421580419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86296294800779550947720279 129444442201169326421580419)
      ·
        refine ⟨194166663301753989632370629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129444442201169326421580419 194166663301753989632370629)
        ·
          refine ⟨36406249369078873056069493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194166663301753989632370629 36406249369078873056069493)
          ·
            refine ⟨3413085878351144349006515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36406249369078873056069493 3413085878351144349006515)
            ·
              refine ⟨5119628817526716523509773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413085878351144349006515 5119628817526716523509773)
              ·
                refine ⟨1919860806572518696316165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5119628817526716523509773 1919860806572518696316165)
                ·
                  refine ⟨359973901232347255559281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919860806572518696316165 359973901232347255559281)
                  ·
                    rfl

theorem cell21_1577355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_1577355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577355 prefixEnd_1577355 := by exact prefixLift 1577355
  have htrace : WordTrace (prefixWord ++ tailWord_1577355) baseStart_1577355 baseEnd_1577355 := by
    simpa [prefixWord, tailWord_1577355, baseEnd_1577355] using wordTrace_append hprefix tailTrace_1577355
  have hstable : (prefixWord ++ tailWord_1577355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577355).length < 2 ^ (prefixWord ++ tailWord_1577355).sum := by decide
  have hdescent : baseEnd_1577355 < baseStart_1577355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577389 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1577389 : Nat := 118140960795 + 1577389 * 2 ^ 59
def prefixEnd_1577389 : Nat := 4983230072969 + 3 ^ 40 * 1577389 * 2
def baseEnd_1577389 : Nat := 359981660495570751992545

theorem tailTrace_1577389 : CollatzResearch.WordTrace tailWord_1577389 prefixEnd_1577389 359981660495570751992545 := by
  unfold tailWord_1577389
  simp only [CollatzResearch.WordTrace]
  refine ⟨57532103282396524438551221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38354735521597682959034147 57532103282396524438551221)
  ·
    refine ⟨5393634682724674166114177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57532103282396524438551221 5393634682724674166114177)
    ·
      refine ⟨4045226012043505624585633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5393634682724674166114177 4045226012043505624585633)
      ·
        refine ⟨3033919509032629218439225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045226012043505624585633 3033919509032629218439225)
        ·
          refine ⟨2275439631774471913829419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3033919509032629218439225 2275439631774471913829419)
          ·
            refine ⟨3413159447661707870744129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275439631774471913829419 3413159447661707870744129)
            ·
              refine ⟨2559869585746280903058097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413159447661707870744129 2559869585746280903058097)
              ·
                refine ⟨1919902189309710677293573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559869585746280903058097 1919902189309710677293573)
                ·
                  refine ⟨359981660495570751992545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919902189309710677293573 359981660495570751992545)
                  ·
                    rfl

theorem cell21_1577389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1577389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577389 prefixEnd_1577389 := by exact prefixLift 1577389
  have htrace : WordTrace (prefixWord ++ tailWord_1577389) baseStart_1577389 baseEnd_1577389 := by
    simpa [prefixWord, tailWord_1577389, baseEnd_1577389] using wordTrace_append hprefix tailTrace_1577389
  have hstable : (prefixWord ++ tailWord_1577389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577389).length < 2 ^ (prefixWord ++ tailWord_1577389).sum := by decide
  have hdescent : baseEnd_1577389 < baseStart_1577389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577448 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 4]
def baseStart_1577448 : Nat := 118140960795 + 1577448 * 2 ^ 59
def prefixEnd_1577448 : Nat := 4983230072969 + 3 ^ 40 * 1577448 * 2
def baseEnd_1577448 : Nat := 359995125099399760509091

theorem tailTrace_1577448 : CollatzResearch.WordTrace tailWord_1577448 prefixEnd_1577448 359995125099399760509091 := by
  unfold tailWord_1577448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767127594591388757474499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38356170126121851676632665 28767127594591388757474499)
  ·
    refine ⟨43150691391887083136211749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767127594591388757474499 43150691391887083136211749)
    ·
      refine ⟨8090754635978828088039703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43150691391887083136211749 8090754635978828088039703)
      ·
        refine ⟨12136131953968242132059555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8090754635978828088039703 12136131953968242132059555)
        ·
          refine ⟨18204197930952363198089333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136131953968242132059555 18204197930952363198089333)
          ·
            refine ⟨1706643556026784049820875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18204197930952363198089333 1706643556026784049820875)
            ·
              refine ⟨2559965334040176074731313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706643556026784049820875 2559965334040176074731313)
              ·
                refine ⟨1919974000530132056048485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559965334040176074731313 1919974000530132056048485)
                ·
                  refine ⟨359995125099399760509091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1919974000530132056048485 359995125099399760509091)
                  ·
                    rfl

theorem cell21_1577448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_1577448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577448 prefixEnd_1577448 := by exact prefixLift 1577448
  have htrace : WordTrace (prefixWord ++ tailWord_1577448) baseStart_1577448 baseEnd_1577448 := by
    simpa [prefixWord, tailWord_1577448, baseEnd_1577448] using wordTrace_append hprefix tailTrace_1577448
  have hstable : (prefixWord ++ tailWord_1577448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577448).length < 2 ^ (prefixWord ++ tailWord_1577448).sum := by decide
  have hdescent : baseEnd_1577448 < baseStart_1577448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577479 : List Nat := [1, 1, 4, 3, 3, 2, 2, 5]
def baseStart_1577479 : Nat := 118140960795 + 1577479 * 2 ^ 59
def prefixEnd_1577479 : Nat := 4983230072969 + 3 ^ 40 * 1577479 * 2
def baseEnd_1577479 : Nat := 120000733240583531830787

theorem tailTrace_1577479 : CollatzResearch.WordTrace tailWord_1577479 prefixEnd_1577479 120000733240583531830787 := by
  unfold tailWord_1577479
  simp only [CollatzResearch.WordTrace]
  refine ⟨57535385852070469809327491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38356923901380313206218327 57535385852070469809327491)
  ·
    refine ⟨86303078778105704713991237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57535385852070469809327491 86303078778105704713991237)
    ·
      refine ⟨16181827270894819633873357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86303078778105704713991237 16181827270894819633873357)
      ·
        refine ⟨6068185226585557362702509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16181827270894819633873357 6068185226585557362702509)
        ·
          refine ⟨2275569459969584011013441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6068185226585557362702509 2275569459969584011013441)
          ·
            refine ⟨1706677094977188008260081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275569459969584011013441 1706677094977188008260081)
            ·
              refine ⟨1280007821232891006195061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706677094977188008260081 1280007821232891006195061)
              ·
                refine ⟨120000733240583531830787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280007821232891006195061 120000733240583531830787)
                ·
                  rfl

theorem cell21_1577479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].length) (baseStart_1577479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577479 prefixEnd_1577479 := by exact prefixLift 1577479
  have htrace : WordTrace (prefixWord ++ tailWord_1577479) baseStart_1577479 baseEnd_1577479 := by
    simpa [prefixWord, tailWord_1577479, baseEnd_1577479] using wordTrace_append hprefix tailTrace_1577479
  have hstable : (prefixWord ++ tailWord_1577479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577479).length < 2 ^ (prefixWord ++ tailWord_1577479).sum := by decide
  have hdescent : baseEnd_1577479 < baseStart_1577479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577535 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_1577535 : Nat := 118140960795 + 1577535 * 2 ^ 59
def prefixEnd_1577535 : Nat := 4983230072969 + 3 ^ 40 * 1577535 * 2
def baseEnd_1577535 : Nat := 360014979684706942558913

theorem tailTrace_1577535 : CollatzResearch.WordTrace tailWord_1577535 prefixEnd_1577535 360014979684706942558913 := by
  unfold tailWord_1577535
  simp only [CollatzResearch.WordTrace]
  refine ⟨57537428339867591373366059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38358285559911727582244039 57537428339867591373366059)
  ·
    refine ⟨86306142509801387060049089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57537428339867591373366059 86306142509801387060049089)
    ·
      refine ⟨64729606882351040295036817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86306142509801387060049089 64729606882351040295036817)
      ·
        refine ⟨48547205161763280221277613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64729606882351040295036817 48547205161763280221277613)
        ·
          refine ⟨18205201935661230082979105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48547205161763280221277613 18205201935661230082979105)
          ·
            refine ⟨13653901451745922562234329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18205201935661230082979105 13653901451745922562234329)
            ·
              refine ⟨10240426088809441921675747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13653901451745922562234329 10240426088809441921675747)
              ·
                refine ⟨15360639133214162882513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240426088809441921675747 15360639133214162882513621)
                ·
                  refine ⟨360014979684706942558913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15360639133214162882513621 360014979684706942558913)
                  ·
                    rfl

theorem cell21_1577535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_1577535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577535 prefixEnd_1577535 := by exact prefixLift 1577535
  have htrace : WordTrace (prefixWord ++ tailWord_1577535) baseStart_1577535 baseEnd_1577535 := by
    simpa [prefixWord, tailWord_1577535, baseEnd_1577535] using wordTrace_append hprefix tailTrace_1577535
  have hstable : (prefixWord ++ tailWord_1577535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577535).length < 2 ^ (prefixWord ++ tailWord_1577535).sum := by decide
  have hdescent : baseEnd_1577535 < baseStart_1577535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577569 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 3]
def baseStart_1577569 : Nat := 118140960795 + 1577569 * 2 ^ 59
def prefixEnd_1577569 : Nat := 4983230072969 + 3 ^ 40 * 1577569 * 2
def baseEnd_1577569 : Nat := 360022738947930438992177

theorem tailTrace_1577569 : CollatzResearch.WordTrace tailWord_1577569 prefixEnd_1577569 360022738947930438992177 := by
  unfold tailWord_1577569
  simp only [CollatzResearch.WordTrace]
  refine ⟨57538668421744415180103761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38359112281162943453402507 57538668421744415180103761)
  ·
    refine ⟨43154001316308311385077821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57538668421744415180103761 43154001316308311385077821)
    ·
      refine ⟨16182750493615616769404183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43154001316308311385077821 16182750493615616769404183)
      ·
        refine ⟨24274125740423425154106275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182750493615616769404183 24274125740423425154106275)
        ·
          refine ⟨36411188610635137731159413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24274125740423425154106275 36411188610635137731159413)
          ·
            refine ⟨3413548932247044162296195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36411188610635137731159413 3413548932247044162296195)
            ·
              refine ⟨5120323398370566243444293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3413548932247044162296195 5120323398370566243444293)
              ·
                refine ⟨960060637194481170645805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5120323398370566243444293 960060637194481170645805)
                ·
                  refine ⟨360022738947930438992177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960060637194481170645805 360022738947930438992177)
                  ·
                    rfl

theorem cell21_1577569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_1577569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577569 prefixEnd_1577569 := by exact prefixLift 1577569
  have htrace : WordTrace (prefixWord ++ tailWord_1577569) baseStart_1577569 baseEnd_1577569 := by
    simpa [prefixWord, tailWord_1577569, baseEnd_1577569] using wordTrace_append hprefix tailTrace_1577569
  have hstable : (prefixWord ++ tailWord_1577569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577569).length < 2 ^ (prefixWord ++ tailWord_1577569).sum := by decide
  have hdescent : baseEnd_1577569 < baseStart_1577569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577628 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1577628 : Nat := 118140960795 + 1577628 * 2 ^ 59
def prefixEnd_1577628 : Nat := 4983230072969 + 3 ^ 40 * 1577628 * 2
def baseEnd_1577628 : Nat := 360036203551759447508723

theorem tailTrace_1577628 : CollatzResearch.WordTrace tailWord_1577628 prefixEnd_1577628 360036203551759447508723 := by
  unfold tailWord_1577628
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770410164265334128250769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38360546885687112171001025 28770410164265334128250769)
  ·
    refine ⟨21577807623199000596188077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28770410164265334128250769 21577807623199000596188077)
    ·
      refine ⟨8091677858699625223570529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21577807623199000596188077 8091677858699625223570529)
      ·
        refine ⟨6068758394024718917677897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8091677858699625223570529 6068758394024718917677897)
        ·
          refine ⟨4551568795518539188258423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6068758394024718917677897 4551568795518539188258423)
          ·
            refine ⟨6827353193277808782387635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551568795518539188258423 6827353193277808782387635)
            ·
              refine ⟨10241029789916713173581453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827353193277808782387635 10241029789916713173581453)
              ·
                refine ⟨3840386171218767440093045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10241029789916713173581453 3840386171218767440093045)
                ·
                  refine ⟨360036203551759447508723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3840386171218767440093045 360036203551759447508723)
                  ·
                    rfl

theorem cell21_1577628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1577628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577628 prefixEnd_1577628 := by exact prefixLift 1577628
  have htrace : WordTrace (prefixWord ++ tailWord_1577628) baseStart_1577628 baseEnd_1577628 := by
    simpa [prefixWord, tailWord_1577628, baseEnd_1577628] using wordTrace_append hprefix tailTrace_1577628
  have hstable : (prefixWord ++ tailWord_1577628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577628).length < 2 ^ (prefixWord ++ tailWord_1577628).sum := by decide
  have hdescent : baseEnd_1577628 < baseStart_1577628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577735 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_1577735 : Nat := 118140960795 + 1577735 * 2 ^ 59
def prefixEnd_1577735 : Nat := 4983230072969 + 3 ^ 40 * 1577735 * 2
def baseEnd_1577735 : Nat := 360060622409551039225171

theorem tailTrace_1577735 : CollatzResearch.WordTrace tailWord_1577735 prefixEnd_1577735 360060622409551039225171 := by
  unfold tailWord_1577735
  simp only [CollatzResearch.WordTrace]
  refine ⟨57544722939143025530646659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38363148626095350353764439 57544722939143025530646659)
  ·
    refine ⟨86317084408714538295969989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57544722939143025530646659 86317084408714538295969989)
    ·
      refine ⟨16184453326633975930494373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86317084408714538295969989 16184453326633975930494373)
      ·
        refine ⟨3034584998743870486967695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16184453326633975930494373 3034584998743870486967695)
        ·
          refine ⟨4551877498115805730451543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034584998743870486967695 4551877498115805730451543)
          ·
            refine ⟨6827816247173708595677315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551877498115805730451543 6827816247173708595677315)
            ·
              refine ⟨10241724370760562893515973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6827816247173708595677315 10241724370760562893515973)
              ·
                refine ⟨1920323319517605542534245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10241724370760562893515973 1920323319517605542534245)
                ·
                  refine ⟨360060622409551039225171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920323319517605542534245 360060622409551039225171)
                  ·
                    rfl

theorem cell21_1577735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_1577735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577735 prefixEnd_1577735 := by exact prefixLift 1577735
  have htrace : WordTrace (prefixWord ++ tailWord_1577735) baseStart_1577735 baseEnd_1577735 := by
    simpa [prefixWord, tailWord_1577735, baseEnd_1577735] using wordTrace_append hprefix tailTrace_1577735
  have hstable : (prefixWord ++ tailWord_1577735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577735).length < 2 ^ (prefixWord ++ tailWord_1577735).sum := by decide
  have hdescent : baseEnd_1577735 < baseStart_1577735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577901 : List Nat := [1, 5, 2, 3, 10]
def baseStart_1577901 : Nat := 118140960795 + 1577901 * 2 ^ 59
def prefixEnd_1577901 : Nat := 4983230072969 + 3 ^ 40 * 1577901 * 2
def baseEnd_1577901 : Nat := 4445660566310760980965

theorem tailTrace_1577901 : CollatzResearch.WordTrace tailWord_1577901 prefixEnd_1577901 4445660566310760980965 := by
  unfold tailWord_1577901
  simp only [CollatzResearch.WordTrace]
  refine ⟨57550777456541635881189557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38367184971027757254126371 57550777456541635881189557)
  ·
    refine ⟨5395385386550778363861521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57550777456541635881189557 5395385386550778363861521)
    ·
      refine ⟨4046539039913083772896141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5395385386550778363861521 4046539039913083772896141)
      ·
        refine ⟨1517452139967406414836053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4046539039913083772896141 1517452139967406414836053)
        ·
          refine ⟨4445660566310760980965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1517452139967406414836053 4445660566310760980965)
          ·
            rfl

theorem cell21_1577901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 10].length) (baseStart_1577901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577901 prefixEnd_1577901 := by exact prefixLift 1577901
  have htrace : WordTrace (prefixWord ++ tailWord_1577901) baseStart_1577901 baseEnd_1577901 := by
    simpa [prefixWord, tailWord_1577901, baseEnd_1577901] using wordTrace_append hprefix tailTrace_1577901
  have hstable : (prefixWord ++ tailWord_1577901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577901).length < 2 ^ (prefixWord ++ tailWord_1577901).sum := by decide
  have hdescent : baseEnd_1577901 < baseStart_1577901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577949 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 3]
def baseStart_1577949 : Nat := 118140960795 + 1577949 * 2 ^ 59
def prefixEnd_1577949 : Nat := 4983230072969 + 3 ^ 40 * 1577949 * 2
def baseEnd_1577949 : Nat := 360109460125134222658067

theorem tailTrace_1577949 : CollatzResearch.WordTrace tailWord_1577949 prefixEnd_1577949 360109460125134222658067 := by
  unfold tailWord_1577949
  simp only [CollatzResearch.WordTrace]
  refine ⟨57552528160367740078936901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38368352106911826719291267 57552528160367740078936901)
  ·
    refine ⟨10791099030068951264800669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57552528160367740078936901 10791099030068951264800669)
    ·
      refine ⟨4046662136275856724300251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10791099030068951264800669 4046662136275856724300251)
      ·
        refine ⟨6069993204413785086450377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046662136275856724300251 6069993204413785086450377)
        ·
          refine ⟨4552494903310338814837783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6069993204413785086450377 4552494903310338814837783)
          ·
            refine ⟨6828742354965508222256675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552494903310338814837783 6828742354965508222256675)
            ·
              refine ⟨10243113532448262333385013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6828742354965508222256675 10243113532448262333385013)
              ·
                refine ⟨960291893667024593754845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10243113532448262333385013 960291893667024593754845)
                ·
                  refine ⟨360109460125134222658067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960291893667024593754845 360109460125134222658067)
                  ·
                    rfl

theorem cell21_1577949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_1577949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577949 prefixEnd_1577949 := by exact prefixLift 1577949
  have htrace : WordTrace (prefixWord ++ tailWord_1577949) baseStart_1577949 baseEnd_1577949 := by
    simpa [prefixWord, tailWord_1577949, baseEnd_1577949] using wordTrace_append hprefix tailTrace_1577949
  have hstable : (prefixWord ++ tailWord_1577949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577949).length < 2 ^ (prefixWord ++ tailWord_1577949).sum := by decide
  have hdescent : baseEnd_1577949 < baseStart_1577949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577991 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 5]
def baseStart_1577991 : Nat := 118140960795 + 1577991 * 2 ^ 59
def prefixEnd_1577991 : Nat := 4983230072969 + 3 ^ 40 * 1577991 * 2
def baseEnd_1577991 : Nat := 360119045097351482957981

theorem tailTrace_1577991 : CollatzResearch.WordTrace tailWord_1577991 prefixEnd_1577991 360119045097351482957981 := by
  unfold tailWord_1577991
  simp only [CollatzResearch.WordTrace]
  refine ⟨57554060026215581251965827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38369373350810387501310551 57554060026215581251965827)
  ·
    refine ⟨86331090039323371877948741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57554060026215581251965827 86331090039323371877948741)
    ·
      refine ⟨16187079382373132227115389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86331090039323371877948741 16187079382373132227115389)
      ·
        refine ⟨6070154768389924585168271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16187079382373132227115389 6070154768389924585168271)
        ·
          refine ⟨9105232152584886877752407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6070154768389924585168271 9105232152584886877752407)
          ·
            refine ⟨13657848228877330316628611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105232152584886877752407 13657848228877330316628611)
            ·
              refine ⟨20486772343315995474942917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13657848228877330316628611 20486772343315995474942917)
              ·
                refine ⟨3841269814371749151551797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20486772343315995474942917 3841269814371749151551797)
                ·
                  refine ⟨360119045097351482957981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841269814371749151551797 360119045097351482957981)
                  ·
                    rfl

theorem cell21_1577991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_1577991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577991 prefixEnd_1577991 := by exact prefixLift 1577991
  have htrace : WordTrace (prefixWord ++ tailWord_1577991) baseStart_1577991 baseEnd_1577991 := by
    simpa [prefixWord, tailWord_1577991, baseEnd_1577991] using wordTrace_append hprefix tailTrace_1577991
  have hstable : (prefixWord ++ tailWord_1577991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577991).length < 2 ^ (prefixWord ++ tailWord_1577991).sum := by decide
  have hdescent : baseEnd_1577991 < baseStart_1577991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1577994 : List Nat := [3, 1, 2, 2, 3, 3, 2, 5]
def baseStart_1577994 : Nat := 118140960795 + 1577994 * 2 ^ 59
def prefixEnd_1577994 : Nat := 4983230072969 + 3 ^ 40 * 1577994 * 2
def baseEnd_1577994 : Nat := 120039909912741381469325

theorem tailTrace_1577994 : CollatzResearch.WordTrace tailWord_1577994 prefixEnd_1577994 120039909912741381469325 := by
  unfold tailWord_1577994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14388542361301178191081259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38369446296803141842883357 14388542361301178191081259)
  ·
    refine ⟨21582813541951767286621889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14388542361301178191081259 21582813541951767286621889)
    ·
      refine ⟨16187110156463825464966417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21582813541951767286621889 16187110156463825464966417)
      ·
        refine ⟨12140332617347869098724813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16187110156463825464966417 12140332617347869098724813)
        ·
          refine ⟨4552624731505450912021805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12140332617347869098724813 4552624731505450912021805)
          ·
            refine ⟨1707234274314544092008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552624731505450912021805 1707234274314544092008177)
            ·
              refine ⟨1280425705735908069006133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1707234274314544092008177 1280425705735908069006133)
              ·
                refine ⟨120039909912741381469325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280425705735908069006133 120039909912741381469325)
                ·
                  rfl

theorem cell21_1577994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_1577994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1577994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1577994 prefixEnd_1577994 := by exact prefixLift 1577994
  have htrace : WordTrace (prefixWord ++ tailWord_1577994) baseStart_1577994 baseEnd_1577994 := by
    simpa [prefixWord, tailWord_1577994, baseEnd_1577994] using wordTrace_append hprefix tailTrace_1577994
  have hstable : (prefixWord ++ tailWord_1577994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1577994).length < 2 ^ (prefixWord ++ tailWord_1577994).sum := by decide
  have hdescent : baseEnd_1577994 < baseStart_1577994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1577994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578070 : List Nat := [5, 2, 2, 1, 2, 9]
def baseStart_1578070 : Nat := 118140960795 + 1578070 * 2 ^ 59
def prefixEnd_1578070 : Nat := 4983230072969 + 3 ^ 40 * 1578070 * 2
def baseEnd_1578070 : Nat := 13338410147172774116339

theorem tailTrace_1578070 : CollatzResearch.WordTrace tailWord_1578070 prefixEnd_1578070 13338410147172774116339 := by
  unfold tailWord_1578070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597308837058086109005729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38371294261952918496061109 3597308837058086109005729)
  ·
    refine ⟨2697981627793564581754297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3597308837058086109005729 2697981627793564581754297)
    ·
      refine ⟨2023486220845173436315723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2697981627793564581754297 2023486220845173436315723)
      ·
        refine ⟨3035229331267760154473585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023486220845173436315723 3035229331267760154473585)
        ·
          refine ⟨2276421998450820115855189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035229331267760154473585 2276421998450820115855189)
          ·
            refine ⟨13338410147172774116339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2276421998450820115855189 13338410147172774116339)
            ·
              rfl

theorem cell21_1578070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 9].length) (baseStart_1578070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578070 prefixEnd_1578070 := by exact prefixLift 1578070
  have htrace : WordTrace (prefixWord ++ tailWord_1578070) baseStart_1578070 baseEnd_1578070 := by
    simpa [prefixWord, tailWord_1578070, baseEnd_1578070] using wordTrace_append hprefix tailTrace_1578070
  have hstable : (prefixWord ++ tailWord_1578070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578070).length < 2 ^ (prefixWord ++ tailWord_1578070).sum := by decide
  have hdescent : baseEnd_1578070 < baseStart_1578070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578081 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 6]
def baseStart_1578081 : Nat := 118140960795 + 1578081 * 2 ^ 59
def prefixEnd_1578081 : Nat := 4983230072969 + 3 ^ 40 * 1578081 * 2
def baseEnd_1578081 : Nat := 360139584323531326457797

theorem tailTrace_1578081 : CollatzResearch.WordTrace tailWord_1578081 prefixEnd_1578081 360139584323531326457797 := by
  unfold tailWord_1578081
  simp only [CollatzResearch.WordTrace]
  refine ⟨57557342595889526622742097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38371561730593017748494731 57557342595889526622742097)
  ·
    refine ⟨43168006946917144967056573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57557342595889526622742097 43168006946917144967056573)
    ·
      refine ⟨16188002605093929362646215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43168006946917144967056573 16188002605093929362646215)
      ·
        refine ⟨24282003907640894043969323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16188002605093929362646215 24282003907640894043969323)
        ·
          refine ⟨36423005861461341065953985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24282003907640894043969323 36423005861461341065953985)
          ·
            refine ⟨27317254396096005799465489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36423005861461341065953985 27317254396096005799465489)
            ·
              refine ⟨20487940797072004349599117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27317254396096005799465489 20487940797072004349599117)
              ·
                refine ⟨7682977798902001631099669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20487940797072004349599117 7682977798902001631099669)
                ·
                  refine ⟨360139584323531326457797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7682977798902001631099669 360139584323531326457797)
                  ·
                    rfl

theorem cell21_1578081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_1578081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578081 prefixEnd_1578081 := by exact prefixLift 1578081
  have htrace : WordTrace (prefixWord ++ tailWord_1578081) baseStart_1578081 baseEnd_1578081 := by
    simpa [prefixWord, tailWord_1578081, baseEnd_1578081] using wordTrace_append hprefix tailTrace_1578081
  have hstable : (prefixWord ++ tailWord_1578081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578081).length < 2 ^ (prefixWord ++ tailWord_1578081).sum := by decide
  have hdescent : baseEnd_1578081 < baseStart_1578081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578098 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1578098 : Nat := 118140960795 + 1578098 * 2 ^ 59
def prefixEnd_1578098 : Nat := 4983230072969 + 3 ^ 40 * 1578098 * 2
def baseEnd_1578098 : Nat := 360143463955143074674429

theorem tailTrace_1578098 : CollatzResearch.WordTrace tailWord_1578098 prefixEnd_1578098 360143463955143074674429 := by
  unfold tailWord_1578098
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389490659206984631527737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38371975091218625684073965 14389490659206984631527737)
  ·
    refine ⟨10792117994405238473645803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14389490659206984631527737 10792117994405238473645803)
    ·
      refine ⟨16188176991607857710468705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10792117994405238473645803 16188176991607857710468705)
      ·
        refine ⟨12141132743705893282851529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16188176991607857710468705 12141132743705893282851529)
        ·
          refine ⟨9105849557779419962138647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12141132743705893282851529 9105849557779419962138647)
          ·
            refine ⟨13658774336669129943207971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9105849557779419962138647 13658774336669129943207971)
            ·
              refine ⟨20488161505003694914811957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13658774336669129943207971 20488161505003694914811957)
              ·
                refine ⟨1920765141094096398263621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20488161505003694914811957 1920765141094096398263621)
                ·
                  refine ⟨360143463955143074674429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1920765141094096398263621 360143463955143074674429)
                  ·
                    rfl

theorem cell21_1578098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1578098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578098 prefixEnd_1578098 := by exact prefixLift 1578098
  have htrace : WordTrace (prefixWord ++ tailWord_1578098) baseStart_1578098 baseEnd_1578098 := by
    simpa [prefixWord, tailWord_1578098, baseEnd_1578098] using wordTrace_append hprefix tailTrace_1578098
  have hstable : (prefixWord ++ tailWord_1578098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578098).length < 2 ^ (prefixWord ++ tailWord_1578098).sum := by decide
  have hdescent : baseEnd_1578098 < baseStart_1578098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578101 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 5]
def baseStart_1578101 : Nat := 118140960795 + 1578101 * 2 ^ 59
def prefixEnd_1578101 : Nat := 4983230072969 + 3 ^ 40 * 1578101 * 2
def baseEnd_1578101 : Nat := 360144148596015736124423

theorem tailTrace_1578101 : CollatzResearch.WordTrace tailWord_1578101 prefixEnd_1578101 360144148596015736124423 := by
  unfold tailWord_1578101
  simp only [CollatzResearch.WordTrace]
  refine ⟨57558072055817070038470157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38372048037211380025646771 57558072055817070038470157)
  ·
    refine ⟨21584277020931401264426309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57558072055817070038470157 21584277020931401264426309)
    ·
      refine ⟨4047051941424637737079933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21584277020931401264426309 4047051941424637737079933)
      ·
        refine ⟨1517644478034239151404975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4047051941424637737079933 1517644478034239151404975)
        ·
          refine ⟨2276466717051358727107463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517644478034239151404975 2276466717051358727107463)
          ·
            refine ⟨3414700075577038090661195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276466717051358727107463 3414700075577038090661195)
            ·
              refine ⟨5122050113365557135991793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414700075577038090661195 5122050113365557135991793)
              ·
                refine ⟨3841537585024167851993845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5122050113365557135991793 3841537585024167851993845)
                ·
                  refine ⟨360144148596015736124423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3841537585024167851993845 360144148596015736124423)
                  ·
                    rfl

theorem cell21_1578101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_1578101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578101 prefixEnd_1578101 := by exact prefixLift 1578101
  have htrace : WordTrace (prefixWord ++ tailWord_1578101) baseStart_1578101 baseEnd_1578101 := by
    simpa [prefixWord, tailWord_1578101, baseEnd_1578101] using wordTrace_append hprefix tailTrace_1578101
  have hstable : (prefixWord ++ tailWord_1578101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578101).length < 2 ^ (prefixWord ++ tailWord_1578101).sum := by decide
  have hdescent : baseEnd_1578101 < baseStart_1578101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578174 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1578174 : Nat := 118140960795 + 1578174 * 2 ^ 59
def prefixEnd_1578174 : Nat := 4983230072969 + 3 ^ 40 * 1578174 * 2
def baseEnd_1578174 : Nat := 360160808190583831407607

theorem tailTrace_1578174 : CollatzResearch.WordTrace tailWord_1578174 prefixEnd_1578174 360160808190583831407607 := by
  unfold tailWord_1578174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195091823069075438234697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38373823056368402337251717 7195091823069075438234697)
  ·
    refine ⟨5396318867301806578676023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7195091823069075438234697 5396318867301806578676023)
    ·
      refine ⟨8094478300952709868014035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396318867301806578676023 8094478300952709868014035)
      ·
        refine ⟨12141717451429064802021053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8094478300952709868014035 12141717451429064802021053)
        ·
          refine ⟨4553144044285899300757895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12141717451429064802021053 4553144044285899300757895)
          ·
            refine ⟨6829716066428848951136843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553144044285899300757895 6829716066428848951136843)
            ·
              refine ⟨10244574099643273426705265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829716066428848951136843 10244574099643273426705265)
              ·
                refine ⟨7683430574732455070028949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10244574099643273426705265 7683430574732455070028949)
                ·
                  refine ⟨360160808190583831407607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7683430574732455070028949 360160808190583831407607)
                  ·
                    rfl

theorem cell21_1578174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1578174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578174 prefixEnd_1578174 := by exact prefixLift 1578174
  have htrace : WordTrace (prefixWord ++ tailWord_1578174) baseStart_1578174 baseEnd_1578174 := by
    simpa [prefixWord, tailWord_1578174, baseEnd_1578174] using wordTrace_append hprefix tailTrace_1578174
  have hstable : (prefixWord ++ tailWord_1578174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578174).length < 2 ^ (prefixWord ++ tailWord_1578174).sum := by decide
  have hdescent : baseEnd_1578174 < baseStart_1578174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578247 : List Nat := [1, 1, 4, 15]
def baseStart_1578247 : Nat := 118140960795 + 1578247 * 2 ^ 59
def prefixEnd_1578247 : Nat := 4983230072969 + 3 ^ 40 * 1578247 * 2
def baseEnd_1578247 : Nat := 1482211801584987352637

theorem tailTrace_1578247 : CollatzResearch.WordTrace tailWord_1578247 prefixEnd_1578247 1482211801584987352637 := by
  unfold tailWord_1578247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57563397113288136973284995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38375598075525424648856663 57563397113288136973284995)
  ·
    refine ⟨86345095669932205459927493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57563397113288136973284995 86345095669932205459927493)
    ·
      refine ⟨16189705438112288523736405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86345095669932205459927493 16189705438112288523736405)
      ·
        refine ⟨1482211801584987352637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 16189705438112288523736405 1482211801584987352637)
        ·
          rfl

theorem cell21_1578247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 15].length) (baseStart_1578247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578247 prefixEnd_1578247 := by exact prefixLift 1578247
  have htrace : WordTrace (prefixWord ++ tailWord_1578247) baseStart_1578247 baseEnd_1578247 := by
    simpa [prefixWord, tailWord_1578247, baseEnd_1578247] using wordTrace_append hprefix tailTrace_1578247
  have hstable : (prefixWord ++ tailWord_1578247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578247).length < 2 ^ (prefixWord ++ tailWord_1578247).sum := by decide
  have hdescent : baseEnd_1578247 < baseStart_1578247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578264 : List Nat := [2, 1, 2, 3, 1, 3, 3, 6]
def baseStart_1578264 : Nat := 118140960795 + 1578264 * 2 ^ 59
def prefixEnd_1578264 : Nat := 4983230072969 + 3 ^ 40 * 1578264 * 2
def baseEnd_1578264 : Nat := 120060449138921224969141

theorem tailTrace_1578264 : CollatzResearch.WordTrace tailWord_1578264 prefixEnd_1578264 120060449138921224969141 := by
  unfold tailWord_1578264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28782008577113274438326923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38376011436151032584435897 28782008577113274438326923)
  ·
    refine ⟨43173012865669911657490385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28782008577113274438326923 43173012865669911657490385)
    ·
      refine ⟨32379759649252433743117789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43173012865669911657490385 32379759649252433743117789)
      ·
        refine ⟨12142409868469662653669171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32379759649252433743117789 12142409868469662653669171)
        ·
          refine ⟨18213614802704493980503757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12142409868469662653669171 18213614802704493980503757)
          ·
            refine ⟨6830105551014185242688909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18213614802704493980503757 6830105551014185242688909)
            ·
              refine ⟨2561289581630319466008341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6830105551014185242688909 2561289581630319466008341)
              ·
                refine ⟨120060449138921224969141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2561289581630319466008341 120060449138921224969141)
                ·
                  rfl

theorem cell21_1578264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_1578264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578264 prefixEnd_1578264 := by exact prefixLift 1578264
  have htrace : WordTrace (prefixWord ++ tailWord_1578264) baseStart_1578264 baseEnd_1578264 := by
    simpa [prefixWord, tailWord_1578264, baseEnd_1578264] using wordTrace_append hprefix tailTrace_1578264
  have hstable : (prefixWord ++ tailWord_1578264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578264).length < 2 ^ (prefixWord ++ tailWord_1578264).sum := by decide
  have hdescent : baseEnd_1578264 < baseStart_1578264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578301 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 4]
def baseStart_1578301 : Nat := 118140960795 + 1578301 * 2 ^ 59
def prefixEnd_1578301 : Nat := 4983230072969 + 3 ^ 40 * 1578301 * 2
def baseEnd_1578301 : Nat := 360189791320859832790681

theorem tailTrace_1578301 : CollatzResearch.WordTrace tailWord_1578301 prefixEnd_1578301 360189791320859832790681 := by
  unfold tailWord_1578301
  simp only [CollatzResearch.WordTrace]
  refine ⟨57565366655092504195750757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38376911103395002797167171 57565366655092504195750757)
  ·
    refine ⟨10793506247829844536703267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57565366655092504195750757 10793506247829844536703267)
    ·
      refine ⟨16190259371744766805054901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793506247829844536703267 16190259371744766805054901)
      ·
        refine ⟨1517836816101071887973897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16190259371744766805054901 1517836816101071887973897)
        ·
          refine ⟨1138377612075803915980423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517836816101071887973897 1138377612075803915980423)
          ·
            refine ⟨1707566418113705873970635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138377612075803915980423 1707566418113705873970635)
            ·
              refine ⟨2561349627170558810955953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707566418113705873970635 2561349627170558810955953)
              ·
                refine ⟨1921012220377919108216965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561349627170558810955953 1921012220377919108216965)
                ·
                  refine ⟨360189791320859832790681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921012220377919108216965 360189791320859832790681)
                  ·
                    rfl

theorem cell21_1578301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_1578301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578301 prefixEnd_1578301 := by exact prefixLift 1578301
  have htrace : WordTrace (prefixWord ++ tailWord_1578301) baseStart_1578301 baseEnd_1578301 := by
    simpa [prefixWord, tailWord_1578301, baseEnd_1578301] using wordTrace_append hprefix tailTrace_1578301
  have hstable : (prefixWord ++ tailWord_1578301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578301).length < 2 ^ (prefixWord ++ tailWord_1578301).sum := by decide
  have hdescent : baseEnd_1578301 < baseStart_1578301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578323 : List Nat := [1, 1, 1, 2, 1, 1, 6, 8]
def baseStart_1578323 : Nat := 118140960795 + 1578323 * 2 ^ 59
def prefixEnd_1578323 : Nat := 4983230072969 + 3 ^ 40 * 1578323 * 2
def baseEnd_1578323 : Nat := 120064937340197561141323

theorem tailTrace_1578323 : CollatzResearch.WordTrace tailWord_1578323 prefixEnd_1578323 120064937340197561141323 := by
  unfold tailWord_1578323
  simp only [CollatzResearch.WordTrace]
  refine ⟨57566169061012801953051623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38377446040675201302034415 57566169061012801953051623)
  ·
    refine ⟨86349253591519202929577435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57566169061012801953051623 86349253591519202929577435)
    ·
      refine ⟨129523880387278804394366153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86349253591519202929577435 129523880387278804394366153)
      ·
        refine ⟨97142910290459103295774615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129523880387278804394366153 97142910290459103295774615)
        ·
          refine ⟨145714365435688654943661923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97142910290459103295774615 145714365435688654943661923)
          ·
            refine ⟨218571548153532982415492885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145714365435688654943661923 218571548153532982415492885)
            ·
              refine ⟨10245541319696858550726229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 218571548153532982415492885 10245541319696858550726229)
              ·
                refine ⟨120064937340197561141323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10245541319696858550726229 120064937340197561141323)
                ·
                  rfl

theorem cell21_1578323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 8].length) (baseStart_1578323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578323 prefixEnd_1578323 := by exact prefixLift 1578323
  have htrace : WordTrace (prefixWord ++ tailWord_1578323) baseStart_1578323 baseEnd_1578323 := by
    simpa [prefixWord, tailWord_1578323, baseEnd_1578323] using wordTrace_append hprefix tailTrace_1578323
  have hstable : (prefixWord ++ tailWord_1578323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578323).length < 2 ^ (prefixWord ++ tailWord_1578323).sum := by decide
  have hdescent : baseEnd_1578323 < baseStart_1578323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578340 : List Nat := [2, 3, 1, 1, 3, 3, 1, 7]
def baseStart_1578340 : Nat := 118140960795 + 1578340 * 2 ^ 59
def prefixEnd_1578340 : Nat := 4983230072969 + 3 ^ 40 * 1578340 * 2
def baseEnd_1578340 : Nat := 120066230550734810546867

theorem tailTrace_1578340 : CollatzResearch.WordTrace tailWord_1578340 prefixEnd_1578340 120066230550734810546867 := by
  unfold tailWord_1578340
  simp only [CollatzResearch.WordTrace]
  refine ⟨28783394550975606928210237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38377859401300809237613649 28783394550975606928210237)
  ·
    refine ⟨10793772956615852598078839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28783394550975606928210237 10793772956615852598078839)
    ·
      refine ⟨16190659434923778897118259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10793772956615852598078839 16190659434923778897118259)
      ·
        refine ⟨24285989152385668345677389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16190659434923778897118259 24285989152385668345677389)
        ·
          refine ⟨9107245932144625629629021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24285989152385668345677389 9107245932144625629629021)
          ·
            refine ⟨3415217224554234611110883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9107245932144625629629021 3415217224554234611110883)
            ·
              refine ⟨5122825836831351916666325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415217224554234611110883 5122825836831351916666325)
              ·
                refine ⟨120066230550734810546867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5122825836831351916666325 120066230550734810546867)
                ·
                  rfl

theorem cell21_1578340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_1578340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578340 prefixEnd_1578340 := by exact prefixLift 1578340
  have htrace : WordTrace (prefixWord ++ tailWord_1578340) baseStart_1578340 baseEnd_1578340 := by
    simpa [prefixWord, tailWord_1578340, baseEnd_1578340] using wordTrace_append hprefix tailTrace_1578340
  have hstable : (prefixWord ++ tailWord_1578340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578340).length < 2 ^ (prefixWord ++ tailWord_1578340).sum := by decide
  have hdescent : baseEnd_1578340 < baseStart_1578340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578346 : List Nat := [3, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_1578346 : Nat := 118140960795 + 1578346 * 2 ^ 59
def prefixEnd_1578346 : Nat := 4983230072969 + 3 ^ 40 * 1578346 * 2
def baseEnd_1578346 : Nat := 360200060933949754540589

theorem tailTrace_1578346 : CollatzResearch.WordTrace tailWord_1578346 prefixEnd_1578346 360200060933949754540589 := by
  unfold tailWord_1578346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391751984982369220284723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38378005293286317920759261 14391751984982369220284723)
  ·
    refine ⟨21587627977473553830427085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14391751984982369220284723 21587627977473553830427085)
    ·
      refine ⟨8095360491552582686410157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21587627977473553830427085 8095360491552582686410157)
      ·
        refine ⟨3035760184332218507403809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8095360491552582686410157 3035760184332218507403809)
        ·
          refine ⟨2276820138249163880552857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035760184332218507403809 2276820138249163880552857)
          ·
            refine ⟨1707615103686872910414643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276820138249163880552857 1707615103686872910414643)
            ·
              refine ⟨2561422655530309365621965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707615103686872910414643 2561422655530309365621965)
              ·
                refine ⟨960533495823866012108237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2561422655530309365621965 960533495823866012108237)
                ·
                  refine ⟨360200060933949754540589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960533495823866012108237 360200060933949754540589)
                  ·
                    rfl

theorem cell21_1578346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_1578346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578346 prefixEnd_1578346 := by exact prefixLift 1578346
  have htrace : WordTrace (prefixWord ++ tailWord_1578346) baseStart_1578346 baseEnd_1578346 := by
    simpa [prefixWord, tailWord_1578346, baseEnd_1578346] using wordTrace_append hprefix tailTrace_1578346
  have hstable : (prefixWord ++ tailWord_1578346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578346).length < 2 ^ (prefixWord ++ tailWord_1578346).sum := by decide
  have hdescent : baseEnd_1578346 < baseStart_1578346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578357 : List Nat := [1, 3, 4, 1, 3, 2, 7]
def baseStart_1578357 : Nat := 118140960795 + 1578357 * 2 ^ 59
def prefixEnd_1578357 : Nat := 4983230072969 + 3 ^ 40 * 1578357 * 2
def baseEnd_1578357 : Nat := 40022507920424019984137

theorem tailTrace_1578357 : CollatzResearch.WordTrace tailWord_1578357 prefixEnd_1578357 40022507920424019984137 := by
  unfold tailWord_1578357
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567409142889625759789325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378272761926417173192883 57567409142889625759789325)
  ·
    refine ⟨21587778428583609659920997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57567409142889625759789325 21587778428583609659920997)
    ·
      refine ⟨4047708455359426811235187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21587778428583609659920997 4047708455359426811235187)
      ·
        refine ⟨6071562683039140216852781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047708455359426811235187 6071562683039140216852781)
        ·
          refine ⟨2276836006139677581319793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6071562683039140216852781 2276836006139677581319793)
          ·
            refine ⟨1707627004604758185989845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276836006139677581319793 1707627004604758185989845)
            ·
              refine ⟨40022507920424019984137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1707627004604758185989845 40022507920424019984137)
              ·
                rfl

theorem cell21_1578357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 7].length) (baseStart_1578357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578357 prefixEnd_1578357 := by exact prefixLift 1578357
  have htrace : WordTrace (prefixWord ++ tailWord_1578357) baseStart_1578357 baseEnd_1578357 := by
    simpa [prefixWord, tailWord_1578357, baseEnd_1578357] using wordTrace_append hprefix tailTrace_1578357
  have hstable : (prefixWord ++ tailWord_1578357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578357).length < 2 ^ (prefixWord ++ tailWord_1578357).sum := by decide
  have hdescent : baseEnd_1578357 < baseStart_1578357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578371 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 5]
def baseStart_1578371 : Nat := 118140960795 + 1578371 * 2 ^ 59
def prefixEnd_1578371 : Nat := 4983230072969 + 3 ^ 40 * 1578371 * 2
def baseEnd_1578371 : Nat := 360205766274555266623871

theorem tailTrace_1578371 : CollatzResearch.WordTrace tailWord_1578371 prefixEnd_1578371 360205766274555266623871 := by
  unfold tailWord_1578371
  simp only [CollatzResearch.WordTrace]
  refine ⟨57567919764838906150798967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378613176559270767199311 57567919764838906150798967)
  ·
    refine ⟨86351879647258359226198451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57567919764838906150798967 86351879647258359226198451)
    ·
      refine ⟨129527819470887538839297677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86351879647258359226198451 129527819470887538839297677)
      ·
        refine ⟨48572932301582827064736629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129527819470887538839297677 48572932301582827064736629)
        ·
          refine ⟨4553712403273390037319059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48572932301582827064736629 4553712403273390037319059)
          ·
            refine ⟨6830568604910085055978589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553712403273390037319059 6830568604910085055978589)
            ·
              refine ⟨2561463226841281895991971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6830568604910085055978589 2561463226841281895991971)
              ·
                refine ⟨3842194840261922843987957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2561463226841281895991971 3842194840261922843987957)
                ·
                  refine ⟨360205766274555266623871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3842194840261922843987957 360205766274555266623871)
                  ·
                    rfl

theorem cell21_1578371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 5].length) (baseStart_1578371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578371 prefixEnd_1578371 := by exact prefixLift 1578371
  have htrace : WordTrace (prefixWord ++ tailWord_1578371) baseStart_1578371 baseEnd_1578371 := by
    simpa [prefixWord, tailWord_1578371, baseEnd_1578371] using wordTrace_append hprefix tailTrace_1578371
  have hstable : (prefixWord ++ tailWord_1578371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578371).length < 2 ^ (prefixWord ++ tailWord_1578371).sum := by decide
  have hdescent : baseEnd_1578371 < baseStart_1578371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578385 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_1578385 : Nat := 118140960795 + 1578385 * 2 ^ 59
def prefixEnd_1578385 : Nat := 4983230072969 + 3 ^ 40 * 1578385 * 2
def baseEnd_1578385 : Nat := 360208961265294353390509

theorem tailTrace_1578385 : CollatzResearch.WordTrace tailWord_1578385 prefixEnd_1578385 360208961265294353390509 := by
  unfold tailWord_1578385
  simp only [CollatzResearch.WordTrace]
  refine ⟨57568430386788186541808609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38378953591192124361205739 57568430386788186541808609)
  ·
    refine ⟨43176322790091139906356457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57568430386788186541808609 43176322790091139906356457)
    ·
      refine ⟨32382242092568354929767343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43176322790091139906356457 32382242092568354929767343)
      ·
        refine ⟨48573363138852532394651015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32382242092568354929767343 48573363138852532394651015)
        ·
          refine ⟨72860044708278798591976523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48573363138852532394651015 72860044708278798591976523)
          ·
            refine ⟨109290067062418197887964785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72860044708278798591976523 109290067062418197887964785)
            ·
              refine ⟨81967550296813648415973589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109290067062418197887964785 81967550296813648415973589)
              ·
                refine ⟨1921114460081569884749381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81967550296813648415973589 1921114460081569884749381)
                ·
                  refine ⟨360208961265294353390509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921114460081569884749381 360208961265294353390509)
                  ·
                    rfl

theorem cell21_1578385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_1578385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578385 prefixEnd_1578385 := by exact prefixLift 1578385
  have htrace : WordTrace (prefixWord ++ tailWord_1578385) baseStart_1578385 baseEnd_1578385 := by
    simpa [prefixWord, tailWord_1578385, baseEnd_1578385] using wordTrace_append hprefix tailTrace_1578385
  have hstable : (prefixWord ++ tailWord_1578385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578385).length < 2 ^ (prefixWord ++ tailWord_1578385).sum := by decide
  have hdescent : baseEnd_1578385 < baseStart_1578385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578551 : List Nat := [1, 1, 3, 1, 2, 4, 1, 8]
def baseStart_1578551 : Nat := 118140960795 + 1578551 * 2 ^ 59
def prefixEnd_1578551 : Nat := 4983230072969 + 3 ^ 40 * 1578551 * 2
def baseEnd_1578551 : Nat := 120082281575638317874501

theorem tailTrace_1578551 : CollatzResearch.WordTrace tailWord_1578551 prefixEnd_1578551 120082281575638317874501 := by
  unfold tailWord_1578551
  simp only [CollatzResearch.WordTrace]
  refine ⟨57574484904186796892351507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38382989936124531261567671 57574484904186796892351507)
  ·
    refine ⟨86361727356280195338527261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57574484904186796892351507 86361727356280195338527261)
    ·
      refine ⟨32385647758605073251947723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86361727356280195338527261 32385647758605073251947723)
      ·
        refine ⟨48578471637907609877921585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32385647758605073251947723 48578471637907609877921585)
        ·
          refine ⟨36433853728430707408441189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48578471637907609877921585 36433853728430707408441189)
          ·
            refine ⟨6831347574080757639082723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36433853728430707408441189 6831347574080757639082723)
            ·
              refine ⟨10247021361121136458624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831347574080757639082723 10247021361121136458624085)
              ·
                refine ⟨120082281575638317874501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10247021361121136458624085 120082281575638317874501)
                ·
                  rfl

theorem cell21_1578551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 8].length) (baseStart_1578551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578551 prefixEnd_1578551 := by exact prefixLift 1578551
  have htrace : WordTrace (prefixWord ++ tailWord_1578551) baseStart_1578551 baseEnd_1578551 := by
    simpa [prefixWord, tailWord_1578551, baseEnd_1578551] using wordTrace_append hprefix tailTrace_1578551
  have hstable : (prefixWord ++ tailWord_1578551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578551).length < 2 ^ (prefixWord ++ tailWord_1578551).sum := by decide
  have hdescent : baseEnd_1578551 < baseStart_1578551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578678 : List Nat := [5, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1578678 : Nat := 118140960795 + 1578678 * 2 ^ 59
def prefixEnd_1578678 : Nat := 4983230072969 + 3 ^ 40 * 1578678 * 2
def baseEnd_1578678 : Nat := 120091942619063651668859

theorem tailTrace_1578678 : CollatzResearch.WordTrace tailWord_1578678 prefixEnd_1578678 120091942619063651668859 := by
  unfold tailWord_1578678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598694810920418598889043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38386077983151131721483125 3598694810920418598889043)
  ·
    refine ⟨5398042216380627898333565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3598694810920418598889043 5398042216380627898333565)
    ·
      refine ⟨2024265831142735461875087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5398042216380627898333565 2024265831142735461875087)
      ·
        refine ⟨3036398746714103192812631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024265831142735461875087 3036398746714103192812631)
        ·
          refine ⟨4554598120071154789218947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036398746714103192812631 4554598120071154789218947)
          ·
            refine ⟨6831897180106732183828421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554598120071154789218947 6831897180106732183828421)
            ·
              refine ⟨1280980721270012284467829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6831897180106732183828421 1280980721270012284467829)
              ·
                refine ⟨120091942619063651668859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1280980721270012284467829 120091942619063651668859)
                ·
                  rfl

theorem cell21_1578678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1578678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578678 prefixEnd_1578678 := by exact prefixLift 1578678
  have htrace : WordTrace (prefixWord ++ tailWord_1578678) baseStart_1578678 baseEnd_1578678 := by
    simpa [prefixWord, tailWord_1578678, baseEnd_1578678] using wordTrace_append hprefix tailTrace_1578678
  have hstable : (prefixWord ++ tailWord_1578678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578678).length < 2 ^ (prefixWord ++ tailWord_1578678).sum := by decide
  have hdescent : baseEnd_1578678 < baseStart_1578678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578734 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_1578734 : Nat := 118140960795 + 1578734 * 2 ^ 59
def prefixEnd_1578734 : Nat := 4983230072969 + 3 ^ 40 * 1578734 * 2
def baseEnd_1578734 : Nat := 360288607820147302073129

theorem tailTrace_1578734 : CollatzResearch.WordTrace tailWord_1578734 prefixEnd_1578734 360288607820147302073129 := by
  unfold tailWord_1578734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197644932815477393282907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38387439641682546097508837 7197644932815477393282907)
  ·
    refine ⟨10796467399223216089924361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7197644932815477393282907 10796467399223216089924361)
    ·
      refine ⟨8097350549417412067443271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10796467399223216089924361 8097350549417412067443271)
      ·
        refine ⟨12146025824126118101164907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097350549417412067443271 12146025824126118101164907)
        ·
          refine ⟨18219038736189177151747361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146025824126118101164907 18219038736189177151747361)
          ·
            refine ⟨13664279052141882863810521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18219038736189177151747361 13664279052141882863810521)
            ·
              refine ⟨10248209289106412147857891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13664279052141882863810521 10248209289106412147857891)
              ·
                refine ⟨15372313933659618221786837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248209289106412147857891 15372313933659618221786837)
                ·
                  refine ⟨360288607820147302073129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15372313933659618221786837 360288607820147302073129)
                  ·
                    rfl

theorem cell21_1578734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_1578734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578734 prefixEnd_1578734 := by exact prefixLift 1578734
  have htrace : WordTrace (prefixWord ++ tailWord_1578734) baseStart_1578734 baseEnd_1578734 := by
    simpa [prefixWord, tailWord_1578734, baseEnd_1578734] using wordTrace_append hprefix tailTrace_1578734
  have hstable : (prefixWord ++ tailWord_1578734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578734).length < 2 ^ (prefixWord ++ tailWord_1578734).sum := by decide
  have hdescent : baseEnd_1578734 < baseStart_1578734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578796 : List Nat := [2, 2, 1, 1, 1, 6, 3, 5]
def baseStart_1578796 : Nat := 118140960795 + 1578796 * 2 ^ 59
def prefixEnd_1578796 : Nat := 4983230072969 + 3 ^ 40 * 1578796 * 2
def baseEnd_1578796 : Nat := 120100919021616324013223

theorem tailTrace_1578796 : CollatzResearch.WordTrace tailWord_1578796 prefixEnd_1578796 120100919021616324013223 := by
  unfold tailWord_1578796
  simp only [CollatzResearch.WordTrace]
  refine ⟨28791710394149601867510121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38388947192199469156680161 28791710394149601867510121)
  ·
    refine ⟨21593782795612201400632591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28791710394149601867510121 21593782795612201400632591)
    ·
      refine ⟨32390674193418302100948887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21593782795612201400632591 32390674193418302100948887)
      ·
        refine ⟨48586011290127453151423331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32390674193418302100948887 48586011290127453151423331)
        ·
          refine ⟨72879016935191179727134997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48586011290127453151423331 72879016935191179727134997)
          ·
            refine ⟨3416203918837086549709453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72879016935191179727134997 3416203918837086549709453)
            ·
              refine ⟨1281076469563907456141045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3416203918837086549709453 1281076469563907456141045)
              ·
                refine ⟨120100919021616324013223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1281076469563907456141045 120100919021616324013223)
                ·
                  rfl

theorem cell21_1578796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_1578796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578796 prefixEnd_1578796 := by exact prefixLift 1578796
  have htrace : WordTrace (prefixWord ++ tailWord_1578796) baseStart_1578796 baseEnd_1578796 := by
    simpa [prefixWord, tailWord_1578796, baseEnd_1578796] using wordTrace_append hprefix tailTrace_1578796
  have hstable : (prefixWord ++ tailWord_1578796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578796).length < 2 ^ (prefixWord ++ tailWord_1578796).sum := by decide
  have hdescent : baseEnd_1578796 < baseStart_1578796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578855 : List Nat := [1, 1, 5, 1, 2, 1, 3, 7]
def baseStart_1578855 : Nat := 118140960795 + 1578855 * 2 ^ 59
def prefixEnd_1578855 : Nat := 4983230072969 + 3 ^ 40 * 1578855 * 2
def baseEnd_1578855 : Nat := 120105407222892660185405

theorem tailTrace_1578855 : CollatzResearch.WordTrace tailWord_1578855 prefixEnd_1578855 120105407222892660185405 := by
  unfold tailWord_1578855
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585572695085456811418019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38390381796723637874278679 57585572695085456811418019)
  ·
    refine ⟨86378359042628185217127029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57585572695085456811418019 86378359042628185217127029)
    ·
      refine ⟨8097971160246392364105659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86378359042628185217127029 8097971160246392364105659)
      ·
        refine ⟨12146956740369588546158489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097971160246392364105659 12146956740369588546158489)
        ·
          refine ⟨9110217555277191409618867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12146956740369588546158489 9110217555277191409618867)
          ·
            refine ⟨13665326332915787114428301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9110217555277191409618867 13665326332915787114428301)
            ·
              refine ⟨5124497374843420167910613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13665326332915787114428301 5124497374843420167910613)
              ·
                refine ⟨120105407222892660185405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5124497374843420167910613 120105407222892660185405)
                ·
                  rfl

theorem cell21_1578855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 7].length) (baseStart_1578855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578855 prefixEnd_1578855 := by exact prefixLift 1578855
  have htrace : WordTrace (prefixWord ++ tailWord_1578855) baseStart_1578855 baseEnd_1578855 := by
    simpa [prefixWord, tailWord_1578855, baseEnd_1578855] using wordTrace_append hprefix tailTrace_1578855
  have hstable : (prefixWord ++ tailWord_1578855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578855).length < 2 ^ (prefixWord ++ tailWord_1578855).sum := by decide
  have hdescent : baseEnd_1578855 < baseStart_1578855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578878 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1578878 : Nat := 118140960795 + 1578878 * 2 ^ 59
def prefixEnd_1578878 : Nat := 4983230072969 + 3 ^ 40 * 1578878 * 2
def baseEnd_1578878 : Nat := 360321470582035051672835

theorem tailTrace_1578878 : CollatzResearch.WordTrace tailWord_1578878 prefixEnd_1578878 360321470582035051672835 := by
  unfold tailWord_1578878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198301446750266467438161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38390941049334754493003525 7198301446750266467438161)
  ·
    refine ⟨5398726085062699850578621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7198301446750266467438161 5398726085062699850578621)
    ·
      refine ⟨2024522281898512443966983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5398726085062699850578621 2024522281898512443966983)
      ·
        refine ⟨3036783422847768665950475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024522281898512443966983 3036783422847768665950475)
        ·
          refine ⟨4555175134271652998925713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036783422847768665950475 4555175134271652998925713)
          ·
            refine ⟨3416381350703739749194285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555175134271652998925713 3416381350703739749194285)
            ·
              refine ⟨1281143006513902405947857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3416381350703739749194285 1281143006513902405947857)
              ·
                refine ⟨960857254885426804460893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281143006513902405947857 960857254885426804460893)
                ·
                  refine ⟨360321470582035051672835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960857254885426804460893 360321470582035051672835)
                  ·
                    rfl

theorem cell21_1578878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1578878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578878 prefixEnd_1578878 := by exact prefixLift 1578878
  have htrace : WordTrace (prefixWord ++ tailWord_1578878) baseStart_1578878 baseEnd_1578878 := by
    simpa [prefixWord, tailWord_1578878, baseEnd_1578878] using wordTrace_append hprefix tailTrace_1578878
  have hstable : (prefixWord ++ tailWord_1578878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578878).length < 2 ^ (prefixWord ++ tailWord_1578878).sum := by decide
  have hdescent : baseEnd_1578878 < baseStart_1578878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578979 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 3]
def baseStart_1578979 : Nat := 118140960795 + 1578979 * 2 ^ 59
def prefixEnd_1578979 : Nat := 4983230072969 + 3 ^ 40 * 1578979 * 2
def baseEnd_1578979 : Nat := 360344520158081320489295

theorem tailTrace_1578979 : CollatzResearch.WordTrace tailWord_1578979 prefixEnd_1578979 360344520158081320489295 := by
  unfold tailWord_1578979
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590095346636225988931991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38393396897757483992621327 57590095346636225988931991)
  ·
    refine ⟨86385143019954338983397987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57590095346636225988931991 86385143019954338983397987)
    ·
      refine ⟨129577714529931508475096981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86385143019954338983397987 129577714529931508475096981)
      ·
        refine ⟨6073955368590539459770171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 129577714529931508475096981 6073955368590539459770171)
        ·
          refine ⟨9110933052885809189655257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073955368590539459770171 9110933052885809189655257)
          ·
            refine ⟨6833199789664356892241443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110933052885809189655257 6833199789664356892241443)
            ·
              refine ⟨10249799684496535338362165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833199789664356892241443 10249799684496535338362165)
              ·
                refine ⟨960918720421550187971453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10249799684496535338362165 960918720421550187971453)
                ·
                  refine ⟨360344520158081320489295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960918720421550187971453 360344520158081320489295)
                  ·
                    rfl

theorem cell21_1578979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].length) (baseStart_1578979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578979 prefixEnd_1578979 := by exact prefixLift 1578979
  have htrace : WordTrace (prefixWord ++ tailWord_1578979) baseStart_1578979 baseEnd_1578979 := by
    simpa [prefixWord, tailWord_1578979, baseEnd_1578979] using wordTrace_append hprefix tailTrace_1578979
  have hstable : (prefixWord ++ tailWord_1578979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578979).length < 2 ^ (prefixWord ++ tailWord_1578979).sum := by decide
  have hdescent : baseEnd_1578979 < baseStart_1578979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1578993 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_1578993 : Nat := 118140960795 + 1578993 * 2 ^ 59
def prefixEnd_1578993 : Nat := 4983230072969 + 3 ^ 40 * 1578993 * 2
def baseEnd_1578993 : Nat := 360347715148820407255933

theorem tailTrace_1578993 : CollatzResearch.WordTrace tailWord_1578993 prefixEnd_1578993 360347715148820407255933 := by
  unfold tailWord_1578993
  simp only [CollatzResearch.WordTrace]
  refine ⟨57590605968585506379941633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38393737312390337586627755 57590605968585506379941633)
  ·
    refine ⟨43192954476439129784956225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57590605968585506379941633 43192954476439129784956225)
    ·
      refine ⟨32394715857329347338717169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43192954476439129784956225 32394715857329347338717169)
      ·
        refine ⟨24296036892997010504037877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32394715857329347338717169 24296036892997010504037877)
        ·
          refine ⟨2277753458718469734753551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24296036892997010504037877 2277753458718469734753551)
          ·
            refine ⟨3416630188077704602130327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277753458718469734753551 3416630188077704602130327)
            ·
              refine ⟨5124945282116556903195491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416630188077704602130327 5124945282116556903195491)
              ·
                refine ⟨7687417923174835354793237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124945282116556903195491 7687417923174835354793237)
                ·
                  refine ⟨360347715148820407255933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7687417923174835354793237 360347715148820407255933)
                  ·
                    rfl

theorem cell21_1578993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_1578993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1578993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1578993 prefixEnd_1578993 := by exact prefixLift 1578993
  have htrace : WordTrace (prefixWord ++ tailWord_1578993) baseStart_1578993 baseEnd_1578993 := by
    simpa [prefixWord, tailWord_1578993, baseEnd_1578993] using wordTrace_append hprefix tailTrace_1578993
  have hstable : (prefixWord ++ tailWord_1578993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1578993).length < 2 ^ (prefixWord ++ tailWord_1578993).sum := by decide
  have hdescent : baseEnd_1578993 < baseStart_1578993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1578993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579069 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1579069 : Nat := 118140960795 + 1579069 * 2 ^ 59
def prefixEnd_1579069 : Nat := 4983230072969 + 3 ^ 40 * 1579069 * 2
def baseEnd_1579069 : Nat := 360365059384261163989111

theorem tailTrace_1579069 : CollatzResearch.WordTrace tailWord_1579069 prefixEnd_1579069 360365059384261163989111 := by
  unfold tailWord_1579069
  simp only [CollatzResearch.WordTrace]
  refine ⟨57593377916310171359708261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38395585277540114239805507 57593377916310171359708261)
  ·
    refine ⟨10798758359308157129945299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57593377916310171359708261 10798758359308157129945299)
    ·
      refine ⟨16198137538962235694917949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10798758359308157129945299 16198137538962235694917949)
      ·
        refine ⟨6074301577110838385594231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16198137538962235694917949 6074301577110838385594231)
        ·
          refine ⟨9111452365666257578391347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074301577110838385594231 9111452365666257578391347)
          ·
            refine ⟨13667178548499386367587021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111452365666257578391347 13667178548499386367587021)
            ·
              refine ⟨5125191955687269887845133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13667178548499386367587021 5125191955687269887845133)
              ·
                refine ⟨1921946983382726207941925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125191955687269887845133 1921946983382726207941925)
                ·
                  refine ⟨360365059384261163989111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1921946983382726207941925 360365059384261163989111)
                  ·
                    rfl

theorem cell21_1579069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1579069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579069 prefixEnd_1579069 := by exact prefixLift 1579069
  have htrace : WordTrace (prefixWord ++ tailWord_1579069) baseStart_1579069 baseEnd_1579069 := by
    simpa [prefixWord, tailWord_1579069, baseEnd_1579069] using wordTrace_append hprefix tailTrace_1579069
  have hstable : (prefixWord ++ tailWord_1579069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579069).length < 2 ^ (prefixWord ++ tailWord_1579069).sum := by decide
  have hdescent : baseEnd_1579069 < baseStart_1579069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579106 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1579106 : Nat := 118140960795 + 1579106 * 2 ^ 59
def prefixEnd_1579106 : Nat := 4983230072969 + 3 ^ 40 * 1579106 * 2
def baseEnd_1579106 : Nat := 360373503288357321872369

theorem tailTrace_1579106 : CollatzResearch.WordTrace tailWord_1579106 prefixEnd_1579106 360373503288357321872369 := by
  unfold tailWord_1579106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398681854294031669701293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38396484944784084452536781 14398681854294031669701293)
  ·
    refine ⟨5399505695360261876137985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14398681854294031669701293 5399505695360261876137985)
    ·
      refine ⟨4049629271520196407103489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5399505695360261876137985 4049629271520196407103489)
      ·
        refine ⟨3037221953640147305327617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4049629271520196407103489 3037221953640147305327617)
        ·
          refine ⟨2277916465230110478995713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3037221953640147305327617 2277916465230110478995713)
          ·
            refine ⟨1708437348922582859246785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277916465230110478995713 1708437348922582859246785)
            ·
              refine ⟨1281328011691937144435089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708437348922582859246785 1281328011691937144435089)
              ·
                refine ⟨960996008768952858326317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281328011691937144435089 960996008768952858326317)
                ·
                  refine ⟨360373503288357321872369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 960996008768952858326317 360373503288357321872369)
                  ·
                    rfl

theorem cell21_1579106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1579106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579106 prefixEnd_1579106 := by exact prefixLift 1579106
  have htrace : WordTrace (prefixWord ++ tailWord_1579106) baseStart_1579106 baseEnd_1579106 := by
    simpa [prefixWord, tailWord_1579106, baseEnd_1579106] using wordTrace_append hprefix tailTrace_1579106
  have hstable : (prefixWord ++ tailWord_1579106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579106).length < 2 ^ (prefixWord ++ tailWord_1579106).sum := by decide
  have hdescent : baseEnd_1579106 < baseStart_1579106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579159 : List Nat := [1, 1, 3, 3, 4, 1, 8]
def baseStart_1579159 : Nat := 118140960795 + 1579159 * 2 ^ 59
def prefixEnd_1579159 : Nat := 4983230072969 + 3 ^ 40 * 1579159 * 2
def baseEnd_1579159 : Nat := 40042844290049000832103

theorem tailTrace_1579159 : CollatzResearch.WordTrace tailWord_1579159 prefixEnd_1579159 40042844290049000832103 := by
  unfold tailWord_1579159
  simp only [CollatzResearch.WordTrace]
  refine ⟨57596660485984116730484531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38397773657322744486989687 57596660485984116730484531)
  ·
    refine ⟨86394990728976175095726797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57596660485984116730484531 86394990728976175095726797)
    ·
      refine ⟨32398121523366065660897549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86394990728976175095726797 32398121523366065660897549)
      ·
        refine ⟨12149295571262274622836581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32398121523366065660897549 12149295571262274622836581)
        ·
          refine ⟨2277992919611676491781859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12149295571262274622836581 2277992919611676491781859)
          ·
            refine ⟨3416989379417514737672789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277992919611676491781859 3416989379417514737672789)
            ·
              refine ⟨40042844290049000832103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3416989379417514737672789 40042844290049000832103)
              ·
                rfl

theorem cell21_1579159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_1579159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579159 prefixEnd_1579159 := by exact prefixLift 1579159
  have htrace : WordTrace (prefixWord ++ tailWord_1579159) baseStart_1579159 baseEnd_1579159 := by
    simpa [prefixWord, tailWord_1579159, baseEnd_1579159] using wordTrace_append hprefix tailTrace_1579159
  have hstable : (prefixWord ++ tailWord_1579159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579159).length < 2 ^ (prefixWord ++ tailWord_1579159).sum := by decide
  have hdescent : baseEnd_1579159 < baseStart_1579159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579224 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_1579224 : Nat := 118140960795 + 1579224 * 2 ^ 59
def prefixEnd_1579224 : Nat := 4983230072969 + 3 ^ 40 * 1579224 * 2
def baseEnd_1579224 : Nat := 360400432496015338905461

theorem tailTrace_1579224 : CollatzResearch.WordTrace tailWord_1579224 prefixEnd_1579224 360400432496015338905461 := by
  unfold tailWord_1579224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28799515615374316415800363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38399354153832421887733817 28799515615374316415800363)
  ·
    refine ⟨43199273423061474623700545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28799515615374316415800363 43199273423061474623700545)
    ·
      refine ⟨32399455067296105967775409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43199273423061474623700545 32399455067296105967775409)
      ·
        refine ⟨24299591300472079475831557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32399455067296105967775409 24299591300472079475831557)
        ·
          refine ⟨4556173368838514901718417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24299591300472079475831557 4556173368838514901718417)
          ·
            refine ⟨3417130026628886176288813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556173368838514901718417 3417130026628886176288813)
            ·
              refine ⟨1281423759985832316108305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3417130026628886176288813 1281423759985832316108305)
              ·
                refine ⟨961067819989374237081229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281423759985832316108305 961067819989374237081229)
                ·
                  refine ⟨360400432496015338905461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961067819989374237081229 360400432496015338905461)
                  ·
                    rfl

theorem cell21_1579224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_1579224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579224 prefixEnd_1579224 := by exact prefixLift 1579224
  have htrace : WordTrace (prefixWord ++ tailWord_1579224) baseStart_1579224 baseEnd_1579224 := by
    simpa [prefixWord, tailWord_1579224, baseEnd_1579224] using wordTrace_append hprefix tailTrace_1579224
  have hstable : (prefixWord ++ tailWord_1579224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579224).length < 2 ^ (prefixWord ++ tailWord_1579224).sum := by decide
  have hdescent : baseEnd_1579224 < baseStart_1579224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579249 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_1579249 : Nat := 118140960795 + 1579249 * 2 ^ 59
def prefixEnd_1579249 : Nat := 4983230072969 + 3 ^ 40 * 1579249 * 2
def baseEnd_1579249 : Nat := 360406137836620850988743

theorem tailTrace_1579249 : CollatzResearch.WordTrace tailWord_1579249 prefixEnd_1579249 360406137836620850988743 := by
  unfold tailWord_1579249
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599943055658062101260801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38399962037105374734173867 57599943055658062101260801)
  ·
    refine ⟨43199957291743546575945601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57599943055658062101260801 43199957291743546575945601)
    ·
      refine ⟨32399967968807659931959201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43199957291743546575945601 32399967968807659931959201)
      ·
        refine ⟨24299975976605744948969401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32399967968807659931959201 24299975976605744948969401)
        ·
          refine ⟨18224981982454308711727051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24299975976605744948969401 18224981982454308711727051)
          ·
            refine ⟨27337472973681463067590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224981982454308711727051 27337472973681463067590577)
            ·
              refine ⟨20503104730261097300692933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27337472973681463067590577 20503104730261097300692933)
              ·
                refine ⟨3844332136923955743879925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20503104730261097300692933 3844332136923955743879925)
                ·
                  refine ⟨360406137836620850988743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3844332136923955743879925 360406137836620850988743)
                  ·
                    rfl

theorem cell21_1579249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_1579249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579249 prefixEnd_1579249 := by exact prefixLift 1579249
  have htrace : WordTrace (prefixWord ++ tailWord_1579249) baseStart_1579249 baseEnd_1579249 := by
    simpa [prefixWord, tailWord_1579249, baseEnd_1579249] using wordTrace_append hprefix tailTrace_1579249
  have hstable : (prefixWord ++ tailWord_1579249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579249).length < 2 ^ (prefixWord ++ tailWord_1579249).sum := by decide
  have hdescent : baseEnd_1579249 < baseStart_1579249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579446 : List Nat := [5, 1, 15]
def baseStart_1579446 : Nat := 118140960795 + 1579446 * 2 ^ 59
def prefixEnd_1579446 : Nat := 4983230072969 + 3 ^ 40 * 1579446 * 2
def baseEnd_1579446 : Nat := 494445947764872820583

theorem tailTrace_1579446 : CollatzResearch.WordTrace tailWord_1579446 prefixEnd_1579446 494445947764872820583 := by
  unfold tailWord_1579446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600445514746522796636387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38404752157296243164121461 3600445514746522796636387)
  ·
    refine ⟨5400668272119784194954581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3600445514746522796636387 5400668272119784194954581)
    ·
      refine ⟨494445947764872820583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 5400668272119784194954581 494445947764872820583)
      ·
        rfl

theorem cell21_1579446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 15].length) (baseStart_1579446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579446 prefixEnd_1579446 := by exact prefixLift 1579446
  have htrace : WordTrace (prefixWord ++ tailWord_1579446) baseStart_1579446 baseEnd_1579446 := by
    simpa [prefixWord, tailWord_1579446, baseEnd_1579446] using wordTrace_append hprefix tailTrace_1579446
  have hstable : (prefixWord ++ tailWord_1579446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579446).length < 2 ^ (prefixWord ++ tailWord_1579446).sum := by decide
  have hdescent : baseEnd_1579446 < baseStart_1579446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579449 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 4]
def baseStart_1579449 : Nat := 118140960795 + 1579449 * 2 ^ 59
def prefixEnd_1579449 : Nat := 4983230072969 + 3 ^ 40 * 1579449 * 2
def baseEnd_1579449 : Nat := 360451780561464947655001

theorem tailTrace_1579449 : CollatzResearch.WordTrace tailWord_1579449 prefixEnd_1579449 360451780561464947655001 := by
  unfold tailWord_1579449
  simp only [CollatzResearch.WordTrace]
  refine ⟨57607237654933496258541401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38404825103288997505694267 57607237654933496258541401)
  ·
    refine ⟨43205428241200122193906051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57607237654933496258541401 43205428241200122193906051)
    ·
      refine ⟨64808142361800183290859077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43205428241200122193906051 64808142361800183290859077)
      ·
        refine ⟨12151526692837534367036077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64808142361800183290859077 12151526692837534367036077)
        ·
          refine ⟨4556822509814075387638529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12151526692837534367036077 4556822509814075387638529)
          ·
            refine ⟨3417616882360556540728897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556822509814075387638529 3417616882360556540728897)
            ·
              refine ⟨2563212661770417405546673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417616882360556540728897 2563212661770417405546673)
              ·
                refine ⟨1922409496327813054160005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563212661770417405546673 1922409496327813054160005)
                ·
                  refine ⟨360451780561464947655001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1922409496327813054160005 360451780561464947655001)
                  ·
                    rfl

theorem cell21_1579449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 4].length) (baseStart_1579449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579449 prefixEnd_1579449 := by exact prefixLift 1579449
  have htrace : WordTrace (prefixWord ++ tailWord_1579449) baseStart_1579449 baseEnd_1579449 := by
    simpa [prefixWord, tailWord_1579449, baseEnd_1579449] using wordTrace_append hprefix tailTrace_1579449
  have hstable : (prefixWord ++ tailWord_1579449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579449).length < 2 ^ (prefixWord ++ tailWord_1579449).sum := by decide
  have hdescent : baseEnd_1579449 < baseStart_1579449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579452 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1579452 : Nat := 118140960795 + 1579452 * 2 ^ 59
def prefixEnd_1579452 : Nat := 4983230072969 + 3 ^ 40 * 1579452 * 2
def baseEnd_1579452 : Nat := 360452465202337609104995

theorem tailTrace_1579452 : CollatzResearch.WordTrace tailWord_1579452 prefixEnd_1579452 360452465202337609104995 := by
  unfold tailWord_1579452
  simp only [CollatzResearch.WordTrace]
  refine ⟨28803673536961313885450305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38404898049281751847267073 28803673536961313885450305)
  ·
    refine ⟨21602755152720985414087729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28803673536961313885450305 21602755152720985414087729)
    ·
      refine ⟨16202066364540739060565797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21602755152720985414087729 16202066364540739060565797)
      ·
        refine ⟨3037887443351388573856087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16202066364540739060565797 3037887443351388573856087)
        ·
          refine ⟨4556831165027082860784131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037887443351388573856087 4556831165027082860784131)
          ·
            refine ⟨6835246747540624291176197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556831165027082860784131 6835246747540624291176197)
            ·
              refine ⟨1281608765163867054595537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6835246747540624291176197 1281608765163867054595537)
              ·
                refine ⟨961206573872900290946653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281608765163867054595537 961206573872900290946653)
                ·
                  refine ⟨360452465202337609104995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961206573872900290946653 360452465202337609104995)
                  ·
                    rfl

theorem cell21_1579452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1579452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579452 prefixEnd_1579452 := by exact prefixLift 1579452
  have htrace : WordTrace (prefixWord ++ tailWord_1579452) baseStart_1579452 baseEnd_1579452 := by
    simpa [prefixWord, tailWord_1579452, baseEnd_1579452] using wordTrace_append hprefix tailTrace_1579452
  have hstable : (prefixWord ++ tailWord_1579452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579452).length < 2 ^ (prefixWord ++ tailWord_1579452).sum := by decide
  have hdescent : baseEnd_1579452 < baseStart_1579452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579463 : List Nat := [1, 1, 4, 1, 1, 6, 1, 6]
def baseStart_1579463 : Nat := 118140960795 + 1579463 * 2 ^ 59
def prefixEnd_1579463 : Nat := 4983230072969 + 3 ^ 40 * 1579463 * 2
def baseEnd_1579463 : Nat := 120151658517401344807213

theorem tailTrace_1579463 : CollatzResearch.WordTrace tailWord_1579463 prefixEnd_1579463 120151658517401344807213 := by
  unfold tailWord_1579463
  simp only [CollatzResearch.WordTrace]
  refine ⟨57607748276882776649551043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38405165517921851099700695 57607748276882776649551043)
  ·
    refine ⟨86411622415324164974326565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57607748276882776649551043 86411622415324164974326565)
    ·
      refine ⟨16202179202873280932686231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86411622415324164974326565 16202179202873280932686231)
      ·
        refine ⟨24303268804309921399029347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16202179202873280932686231 24303268804309921399029347)
        ·
          refine ⟨36454903206464882098544021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24303268804309921399029347 36454903206464882098544021)
          ·
            refine ⟨1708823587803041348369251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36454903206464882098544021 1708823587803041348369251)
            ·
              refine ⟨2563235381704562022553877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708823587803041348369251 2563235381704562022553877)
              ·
                refine ⟨120151658517401344807213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2563235381704562022553877 120151658517401344807213)
                ·
                  rfl

theorem cell21_1579463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_1579463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579463 prefixEnd_1579463 := by exact prefixLift 1579463
  have htrace : WordTrace (prefixWord ++ tailWord_1579463) baseStart_1579463 baseEnd_1579463 := by
    simpa [prefixWord, tailWord_1579463, baseEnd_1579463] using wordTrace_append hprefix tailTrace_1579463
  have hstable : (prefixWord ++ tailWord_1579463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579463).length < 2 ^ (prefixWord ++ tailWord_1579463).sum := by decide
  have hdescent : baseEnd_1579463 < baseStart_1579463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579477 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_1579477 : Nat := 118140960795 + 1579477 * 2 ^ 59
def prefixEnd_1579477 : Nat := 4983230072969 + 3 ^ 40 * 1579477 * 2
def baseEnd_1579477 : Nat := 360458170542943121188277

theorem tailTrace_1579477 : CollatzResearch.WordTrace tailWord_1579477 prefixEnd_1579477 360458170542943121188277 := by
  unfold tailWord_1579477
  simp only [CollatzResearch.WordTrace]
  refine ⟨57608258898832057040560685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38405505932554704693707123 57608258898832057040560685)
  ·
    refine ⟨21603097087062021390210257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57608258898832057040560685 21603097087062021390210257)
    ·
      refine ⟨16202322815296516042657693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21603097087062021390210257 16202322815296516042657693)
      ·
        refine ⟨6075871055736193515996635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16202322815296516042657693 6075871055736193515996635)
        ·
          refine ⟨9113806583604290273994953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075871055736193515996635 9113806583604290273994953)
          ·
            refine ⟨6835354937703217705496215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9113806583604290273994953 6835354937703217705496215)
            ·
              refine ⟨10253032406554826558244323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835354937703217705496215 10253032406554826558244323)
              ·
                refine ⟨15379548609832239837366485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10253032406554826558244323 15379548609832239837366485)
                ·
                  refine ⟨360458170542943121188277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15379548609832239837366485 360458170542943121188277)
                  ·
                    rfl

theorem cell21_1579477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_1579477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579477 prefixEnd_1579477 := by exact prefixLift 1579477
  have htrace : WordTrace (prefixWord ++ tailWord_1579477) baseStart_1579477 baseEnd_1579477 := by
    simpa [prefixWord, tailWord_1579477, baseEnd_1579477] using wordTrace_append hprefix tailTrace_1579477
  have hstable : (prefixWord ++ tailWord_1579477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579477).length < 2 ^ (prefixWord ++ tailWord_1579477).sum := by decide
  have hdescent : baseEnd_1579477 < baseStart_1579477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579536 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_1579536 : Nat := 118140960795 + 1579536 * 2 ^ 59
def prefixEnd_1579536 : Nat := 4983230072969 + 3 ^ 40 * 1579536 * 2
def baseEnd_1579536 : Nat := 360471635146772129704823

theorem tailTrace_1579536 : CollatzResearch.WordTrace tailWord_1579536 prefixEnd_1579536 360471635146772129704823 := by
  unfold tailWord_1579536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805205402809155058479231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38406940537078873411305641 28805205402809155058479231)
  ·
    refine ⟨43207808104213732587718847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28805205402809155058479231 43207808104213732587718847)
    ·
      refine ⟨64811712156320598881578271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43207808104213732587718847 64811712156320598881578271)
      ·
        refine ⟨97217568234480898322367407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64811712156320598881578271 97217568234480898322367407)
        ·
          refine ⟨145826352351721347483551111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97217568234480898322367407 145826352351721347483551111)
          ·
            refine ⟨218739528527582021225326667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145826352351721347483551111 218739528527582021225326667)
            ·
              refine ⟨328109292791373031837990001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218739528527582021225326667 328109292791373031837990001)
              ·
                refine ⟨246081969593529773878492501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328109292791373031837990001 246081969593529773878492501)
                ·
                  refine ⟨360471635146772129704823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 246081969593529773878492501 360471635146772129704823)
                  ·
                    rfl

theorem cell21_1579536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_1579536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579536 prefixEnd_1579536 := by exact prefixLift 1579536
  have htrace : WordTrace (prefixWord ++ tailWord_1579536) baseStart_1579536 baseEnd_1579536 := by
    simpa [prefixWord, tailWord_1579536, baseEnd_1579536] using wordTrace_append hprefix tailTrace_1579536
  have hstable : (prefixWord ++ tailWord_1579536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579536).length < 2 ^ (prefixWord ++ tailWord_1579536).sum := by decide
  have hdescent : baseEnd_1579536 < baseStart_1579536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579556 : List Nat := [2, 3, 1, 5, 1, 2, 7]
def baseStart_1579556 : Nat := 118140960795 + 1579556 * 2 ^ 59
def prefixEnd_1579556 : Nat := 4983230072969 + 3 ^ 40 * 1579556 * 2
def baseEnd_1579556 : Nat := 40052911046584059930161

theorem tailTrace_1579556 : CollatzResearch.WordTrace tailWord_1579556 prefixEnd_1579556 40052911046584059930161 := by
  unfold tailWord_1579556
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805570132772926766343261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38407426843697235688457681 28805570132772926766343261)
  ·
    refine ⟨10802088799789847537378723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28805570132772926766343261 10802088799789847537378723)
    ·
      refine ⟨16203133199684771306068085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802088799789847537378723 16203133199684771306068085)
      ·
        refine ⟨1519043737470447309943883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16203133199684771306068085 1519043737470447309943883)
        ·
          refine ⟨2278565606205670964915825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519043737470447309943883 2278565606205670964915825)
          ·
            refine ⟨1708924204654253223686869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278565606205670964915825 1708924204654253223686869)
            ·
              refine ⟨40052911046584059930161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1708924204654253223686869 40052911046584059930161)
              ·
                rfl

theorem cell21_1579556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 7].length) (baseStart_1579556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579556 prefixEnd_1579556 := by exact prefixLift 1579556
  have htrace : WordTrace (prefixWord ++ tailWord_1579556) baseStart_1579556 baseEnd_1579556 := by
    simpa [prefixWord, tailWord_1579556, baseEnd_1579556] using wordTrace_append hprefix tailTrace_1579556
  have hstable : (prefixWord ++ tailWord_1579556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579556).length < 2 ^ (prefixWord ++ tailWord_1579556).sum := by decide
  have hdescent : baseEnd_1579556 < baseStart_1579556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579570 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_1579570 : Nat := 118140960795 + 1579570 * 2 ^ 59
def prefixEnd_1579570 : Nat := 4983230072969 + 3 ^ 40 * 1579570 * 2
def baseEnd_1579570 : Nat := 360479394409995626138087

theorem tailTrace_1579570 : CollatzResearch.WordTrace tailWord_1579570 prefixEnd_1579570 360479394409995626138087 := by
  unfold tailWord_1579570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402912721873783480924041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38407767258330089282464109 14402912721873783480924041)
  ·
    refine ⟨10802184541405337610693031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14402912721873783480924041 10802184541405337610693031)
    ·
      refine ⟨16203276812108006416039547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802184541405337610693031 16203276812108006416039547)
      ·
        refine ⟨24304915218162009624059321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16203276812108006416039547 24304915218162009624059321)
        ·
          refine ⟨18228686413621507218044491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24304915218162009624059321 18228686413621507218044491)
          ·
            refine ⟨27343029620432260827066737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18228686413621507218044491 27343029620432260827066737)
            ·
              refine ⟨20507272215324195620300053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27343029620432260827066737 20507272215324195620300053)
              ·
                refine ⟨961278385093321669701565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20507272215324195620300053 961278385093321669701565)
                ·
                  refine ⟨360479394409995626138087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961278385093321669701565 360479394409995626138087)
                  ·
                    rfl

theorem cell21_1579570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_1579570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579570 prefixEnd_1579570 := by exact prefixLift 1579570
  have htrace : WordTrace (prefixWord ++ tailWord_1579570) baseStart_1579570 baseEnd_1579570 := by
    simpa [prefixWord, tailWord_1579570, baseEnd_1579570] using wordTrace_append hprefix tailTrace_1579570
  have hstable : (prefixWord ++ tailWord_1579570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579570).length < 2 ^ (prefixWord ++ tailWord_1579570).sum := by decide
  have hdescent : baseEnd_1579570 < baseStart_1579570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579598 : List Nat := [4, 1, 1, 1, 1, 2, 4, 7]
def baseStart_1579598 : Nat := 118140960795 + 1579598 * 2 ^ 59
def prefixEnd_1579598 : Nat := 4983230072969 + 3 ^ 40 * 1579598 * 2
def baseEnd_1579598 : Nat := 120161928130491266557121

theorem tailTrace_1579598 : CollatzResearch.WordTrace tailWord_1579598 prefixEnd_1579598 120161928130491266557121 := by
  unfold tailWord_1579598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201584016424211838214431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38408448087595796470476965 7201584016424211838214431)
  ·
    refine ⟨10802376024636317757321647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201584016424211838214431 10802376024636317757321647)
    ·
      refine ⟨16203564036954476635982471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802376024636317757321647 16203564036954476635982471)
      ·
        refine ⟨24305346055431714953973707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16203564036954476635982471 24305346055431714953973707)
        ·
          refine ⟨36458019083147572430960561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24305346055431714953973707 36458019083147572430960561)
          ·
            refine ⟨27343514312360679323220421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36458019083147572430960561 27343514312360679323220421)
            ·
              refine ⟨5126908933567627373103829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27343514312360679323220421 5126908933567627373103829)
              ·
                refine ⟨120161928130491266557121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5126908933567627373103829 120161928130491266557121)
                ·
                  rfl

theorem cell21_1579598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_1579598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579598 prefixEnd_1579598 := by exact prefixLift 1579598
  have htrace : WordTrace (prefixWord ++ tailWord_1579598) baseStart_1579598 baseEnd_1579598 := by
    simpa [prefixWord, tailWord_1579598, baseEnd_1579598] using wordTrace_append hprefix tailTrace_1579598
  have hstable : (prefixWord ++ tailWord_1579598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579598).length < 2 ^ (prefixWord ++ tailWord_1579598).sum := by decide
  have hdescent : baseEnd_1579598 < baseStart_1579598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579621 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 3]
def baseStart_1579621 : Nat := 118140960795 + 1579621 * 2 ^ 59
def prefixEnd_1579621 : Nat := 4983230072969 + 3 ^ 40 * 1579621 * 2
def baseEnd_1579621 : Nat := 360491033304830870787983

theorem tailTrace_1579621 : CollatzResearch.WordTrace tailWord_1579621 prefixEnd_1579621 360491033304830870787983 := by
  unfold tailWord_1579621
  simp only [CollatzResearch.WordTrace]
  refine ⟨57613511010310369633802717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38409007340206913089201811 57613511010310369633802717)
  ·
    refine ⟨21605066628866388612676019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57613511010310369633802717 21605066628866388612676019)
    ·
      refine ⟨32407599943299582919014029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21605066628866388612676019 32407599943299582919014029)
      ·
        refine ⟨12152849978737343594630261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32407599943299582919014029 12152849978737343594630261)
        ·
          refine ⟨1139329685506625961996587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12152849978737343594630261 1139329685506625961996587)
          ·
            refine ⟨1708994528259938942994881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139329685506625961996587 1708994528259938942994881)
            ·
              refine ⟨1281745896194954207246161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708994528259938942994881 1281745896194954207246161)
              ·
                refine ⟨961309422146215655434621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281745896194954207246161 961309422146215655434621)
                ·
                  refine ⟨360491033304830870787983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961309422146215655434621 360491033304830870787983)
                  ·
                    rfl

theorem cell21_1579621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_1579621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579621 prefixEnd_1579621 := by exact prefixLift 1579621
  have htrace : WordTrace (prefixWord ++ tailWord_1579621) baseStart_1579621 baseEnd_1579621 := by
    simpa [prefixWord, tailWord_1579621, baseEnd_1579621] using wordTrace_append hprefix tailTrace_1579621
  have hstable : (prefixWord ++ tailWord_1579621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579621).length < 2 ^ (prefixWord ++ tailWord_1579621).sum := by decide
  have hdescent : baseEnd_1579621 < baseStart_1579621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579632 : List Nat := [2, 1, 1, 1, 8, 1, 1, 6]
def baseStart_1579632 : Nat := 118140960795 + 1579632 * 2 ^ 59
def prefixEnd_1579632 : Nat := 4983230072969 + 3 ^ 40 * 1579632 * 2
def baseEnd_1579632 : Nat := 120164514551565765368209

theorem tailTrace_1579632 : CollatzResearch.WordTrace tailWord_1579632 prefixEnd_1579632 120164514551565765368209 := by
  unfold tailWord_1579632
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806956106635259256226575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38409274808847012341635433 28806956106635259256226575)
  ·
    refine ⟨43210434159952888884339863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28806956106635259256226575 43210434159952888884339863)
    ·
      refine ⟨64815651239929333326509795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43210434159952888884339863 64815651239929333326509795)
      ·
        refine ⟨97223476859893999989764693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64815651239929333326509795 97223476859893999989764693)
        ·
          refine ⟨1139337619451882812380055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 97223476859893999989764693 1139337619451882812380055)
          ·
            refine ⟨1709006429177824218570083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139337619451882812380055 1709006429177824218570083)
            ·
              refine ⟨2563509643766736327855125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709006429177824218570083 2563509643766736327855125)
              ·
                refine ⟨120164514551565765368209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2563509643766736327855125 120164514551565765368209)
                ·
                  rfl

theorem cell21_1579632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_1579632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579632 prefixEnd_1579632 := by exact prefixLift 1579632
  have htrace : WordTrace (prefixWord ++ tailWord_1579632) baseStart_1579632 baseEnd_1579632 := by
    simpa [prefixWord, tailWord_1579632, baseEnd_1579632] using wordTrace_append hprefix tailTrace_1579632
  have hstable : (prefixWord ++ tailWord_1579632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579632).length < 2 ^ (prefixWord ++ tailWord_1579632).sum := by decide
  have hdescent : baseEnd_1579632 < baseStart_1579632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579725 : List Nat := [1, 6, 2, 1, 3, 1, 7]
def baseStart_1579725 : Nat := 118140960795 + 1579725 * 2 ^ 59
def prefixEnd_1579725 : Nat := 4983230072969 + 3 ^ 40 * 1579725 * 2
def baseEnd_1579725 : Nat := 40057196391305533450493

theorem tailTrace_1579725 : CollatzResearch.WordTrace tailWord_1579725 prefixEnd_1579725 40057196391305533450493 := by
  unfold tailWord_1579725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57617304201933595395588629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38411536134622396930392419 57617304201933595395588629)
  ·
    refine ⟨2700811134465637284168217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57617304201933595395588629 2700811134465637284168217)
    ·
      refine ⟨2025608350849227963126163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700811134465637284168217 2025608350849227963126163)
      ·
        refine ⟨3038412526273841944689245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025608350849227963126163 3038412526273841944689245)
        ·
          refine ⟨1139404697352690729258467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038412526273841944689245 1139404697352690729258467)
          ·
            refine ⟨1709107046029036093887701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139404697352690729258467 1709107046029036093887701)
            ·
              refine ⟨40057196391305533450493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1709107046029036093887701 40057196391305533450493)
              ·
                rfl

theorem cell21_1579725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 7].length) (baseStart_1579725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579725 prefixEnd_1579725 := by exact prefixLift 1579725
  have htrace : WordTrace (prefixWord ++ tailWord_1579725) baseStart_1579725 baseEnd_1579725 := by
    simpa [prefixWord, tailWord_1579725, baseEnd_1579725] using wordTrace_append hprefix tailTrace_1579725
  have hstable : (prefixWord ++ tailWord_1579725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579725).length < 2 ^ (prefixWord ++ tailWord_1579725).sum := by decide
  have hdescent : baseEnd_1579725 < baseStart_1579725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579846 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1579846 : Nat := 118140960795 + 1579846 * 2 ^ 59
def prefixEnd_1579846 : Nat := 4983230072969 + 3 ^ 40 * 1579846 * 2
def baseEnd_1579846 : Nat := 360542381370280479537523

theorem tailTrace_1579846 : CollatzResearch.WordTrace tailWord_1579846 prefixEnd_1579846 360542381370280479537523 := by
  unfold tailWord_1579846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800678669827976033148231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38414478289663488707162261 1800678669827976033148231)
  ·
    refine ⟨2701018004741964049722347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800678669827976033148231 2701018004741964049722347)
    ·
      refine ⟨4051527007112946074583521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701018004741964049722347 4051527007112946074583521)
      ·
        refine ⟨3038645255334709555937641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051527007112946074583521 3038645255334709555937641)
        ·
          refine ⟨2278983941501032166953231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038645255334709555937641 2278983941501032166953231)
          ·
            refine ⟨3418475912251548250429847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278983941501032166953231 3418475912251548250429847)
            ·
              refine ⟨5127713868377322375644771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418475912251548250429847 5127713868377322375644771)
              ·
                refine ⟨7691570802565983563467157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5127713868377322375644771 7691570802565983563467157)
                ·
                  refine ⟨360542381370280479537523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7691570802565983563467157 360542381370280479537523)
                  ·
                    rfl

theorem cell21_1579846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1579846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579846 prefixEnd_1579846 := by exact prefixLift 1579846
  have htrace : WordTrace (prefixWord ++ tailWord_1579846) baseStart_1579846 baseEnd_1579846 := by
    simpa [prefixWord, tailWord_1579846, baseEnd_1579846] using wordTrace_append hprefix tailTrace_1579846
  have hstable : (prefixWord ++ tailWord_1579846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579846).length < 2 ^ (prefixWord ++ tailWord_1579846).sum := by decide
  have hdescent : baseEnd_1579846 < baseStart_1579846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579961 : List Nat := [1, 2, 1, 4, 2, 11]
def baseStart_1579961 : Nat := 118140960795 + 1579961 * 2 ^ 59
def prefixEnd_1579961 : Nat := 4983230072969 + 3 ^ 40 * 1579961 * 2
def baseEnd_1579961 : Nat := 13354393553224660560023

theorem tailTrace_1579961 : CollatzResearch.WordTrace tailWord_1579961 prefixEnd_1579961 13354393553224660560023 := by
  unfold tailWord_1579961
  simp only [CollatzResearch.WordTrace]
  refine ⟨57625911829078607701179737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38417274552719071800786491 57625911829078607701179737)
  ·
    refine ⟨43219433871808955775884803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57625911829078607701179737 43219433871808955775884803)
    ·
      refine ⟨64829150807713433663827205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43219433871808955775884803 64829150807713433663827205)
      ·
        refine ⟨12155465776446268811967601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64829150807713433663827205 12155465776446268811967601)
        ·
          refine ⟨9116599332334701608975701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12155465776446268811967601 9116599332334701608975701)
          ·
            refine ⟨13354393553224660560023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9116599332334701608975701 13354393553224660560023)
            ·
              rfl

theorem cell21_1579961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 11].length) (baseStart_1579961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579961 prefixEnd_1579961 := by exact prefixLift 1579961
  have htrace : WordTrace (prefixWord ++ tailWord_1579961) baseStart_1579961 baseEnd_1579961 := by
    simpa [prefixWord, tailWord_1579961, baseEnd_1579961] using wordTrace_append hprefix tailTrace_1579961
  have hstable : (prefixWord ++ tailWord_1579961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579961).length < 2 ^ (prefixWord ++ tailWord_1579961).sum := by decide
  have hdescent : baseEnd_1579961 < baseStart_1579961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1579992 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1579992 : Nat := 118140960795 + 1579992 * 2 ^ 59
def prefixEnd_1579992 : Nat := 4983230072969 + 3 ^ 40 * 1579992 * 2
def baseEnd_1579992 : Nat := 360575700559416670103891

theorem tailTrace_1579992 : CollatzResearch.WordTrace tailWord_1579992 prefixEnd_1579992 360575700559416670103891 := by
  unfold tailWord_1579992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28813521245983149997779115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38418028327977533330372153 28813521245983149997779115)
  ·
    refine ⟨43220281868974724996668673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28813521245983149997779115 43220281868974724996668673)
    ·
      refine ⟨32415211401731043747501505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43220281868974724996668673 32415211401731043747501505)
      ·
        refine ⟨24311408551298282810626129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32415211401731043747501505 24311408551298282810626129)
        ·
          refine ⟨18233556413473712107969597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24311408551298282810626129 18233556413473712107969597)
          ·
            refine ⟨6837583655052642040488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18233556413473712107969597 6837583655052642040488599)
            ·
              refine ⟨10256375482578963060732899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6837583655052642040488599 10256375482578963060732899)
              ·
                refine ⟨15384563223868444591099349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10256375482578963060732899 15384563223868444591099349)
                ·
                  refine ⟨360575700559416670103891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15384563223868444591099349 360575700559416670103891)
                  ·
                    rfl

theorem cell21_1579992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1579992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1579992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1579992 prefixEnd_1579992 := by exact prefixLift 1579992
  have htrace : WordTrace (prefixWord ++ tailWord_1579992) baseStart_1579992 baseEnd_1579992 := by
    simpa [prefixWord, tailWord_1579992, baseEnd_1579992] using wordTrace_append hprefix tailTrace_1579992
  have hstable : (prefixWord ++ tailWord_1579992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1579992).length < 2 ^ (prefixWord ++ tailWord_1579992).sum := by decide
  have hdescent : baseEnd_1579992 < baseStart_1579992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1579992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580037 : List Nat := [1, 3, 1, 1, 2, 3, 2, 8]
def baseStart_1580037 : Nat := 118140960795 + 1580037 * 2 ^ 59
def prefixEnd_1580037 : Nat := 4983230072969 + 3 ^ 40 * 1580037 * 2
def baseEnd_1580037 : Nat := 120195323390835530617933

theorem tailTrace_1580037 : CollatzResearch.WordTrace tailWord_1580037 prefixEnd_1580037 120195323390835530617933 := by
  unfold tailWord_1580037
  simp only [CollatzResearch.WordTrace]
  refine ⟨57628683776803272680946365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38419122517868848453964243 57628683776803272680946365)
  ·
    refine ⟨21610756416301227255354887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57628683776803272680946365 21610756416301227255354887)
    ·
      refine ⟨32416134624451840883032331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21610756416301227255354887 32416134624451840883032331)
      ·
        refine ⟨48624201936677761324548497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32416134624451840883032331 48624201936677761324548497)
        ·
          refine ⟨36468151452508320993411373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48624201936677761324548497 36468151452508320993411373)
          ·
            refine ⟨13675556794690620372529265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36468151452508320993411373 13675556794690620372529265)
            ·
              refine ⟨10256667596017965279396949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13675556794690620372529265 10256667596017965279396949)
              ·
                refine ⟨120195323390835530617933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10256667596017965279396949 120195323390835530617933)
                ·
                  rfl

theorem cell21_1580037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_1580037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580037 prefixEnd_1580037 := by exact prefixLift 1580037
  have htrace : WordTrace (prefixWord ++ tailWord_1580037) baseStart_1580037 baseEnd_1580037 := by
    simpa [prefixWord, tailWord_1580037, baseEnd_1580037] using wordTrace_append hprefix tailTrace_1580037
  have hstable : (prefixWord ++ tailWord_1580037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580037).length < 2 ^ (prefixWord ++ tailWord_1580037).sum := by decide
  have hdescent : baseEnd_1580037 < baseStart_1580037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580060 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 3]
def baseStart_1580060 : Nat := 118140960795 + 1580060 * 2 ^ 59
def prefixEnd_1580060 : Nat := 4983230072969 + 3 ^ 40 * 1580060 * 2
def baseEnd_1580060 : Nat := 360591219085863662970419

theorem tailTrace_1580060 : CollatzResearch.WordTrace tailWord_1580060 prefixEnd_1580060 360591219085863662970419 := by
  unfold tailWord_1580060
  simp only [CollatzResearch.WordTrace]
  refine ⟨28814761327859973804516817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38419681770479965072689089 28814761327859973804516817)
  ·
    refine ⟨21611070995894980353387613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28814761327859973804516817 21611070995894980353387613)
    ·
      refine ⟨8104151623460617632520355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21611070995894980353387613 8104151623460617632520355)
      ·
        refine ⟨12156227435190926448780533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8104151623460617632520355 12156227435190926448780533)
        ·
          refine ⟨1139646322049149354573175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12156227435190926448780533 1139646322049149354573175)
          ·
            refine ⟨1709469483073724031859763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139646322049149354573175 1709469483073724031859763)
            ·
              refine ⟨2564204224610586047789645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709469483073724031859763 2564204224610586047789645)
              ·
                refine ⟨961576584228969767921117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2564204224610586047789645 961576584228969767921117)
                ·
                  refine ⟨360591219085863662970419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961576584228969767921117 360591219085863662970419)
                  ·
                    rfl

theorem cell21_1580060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_1580060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580060 prefixEnd_1580060 := by exact prefixLift 1580060
  have htrace : WordTrace (prefixWord ++ tailWord_1580060) baseStart_1580060 baseEnd_1580060 := by
    simpa [prefixWord, tailWord_1580060, baseEnd_1580060] using wordTrace_append hprefix tailTrace_1580060
  have hstable : (prefixWord ++ tailWord_1580060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580060).length < 2 ^ (prefixWord ++ tailWord_1580060).sum := by decide
  have hdescent : baseEnd_1580060 < baseStart_1580060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580071 : List Nat := [1, 1, 7, 1, 1, 3, 7]
def baseStart_1580071 : Nat := 118140960795 + 1580071 * 2 ^ 59
def prefixEnd_1580071 : Nat := 4983230072969 + 3 ^ 40 * 1580071 * 2
def baseEnd_1580071 : Nat := 40065969937303343143007

theorem tailTrace_1580071 : CollatzResearch.WordTrace tailWord_1580071 prefixEnd_1580071 40065969937303343143007 := by
  unfold tailWord_1580071
  simp only [CollatzResearch.WordTrace]
  refine ⟨57629923858680096487684067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38419949239120064325122711 57629923858680096487684067)
  ·
    refine ⟨86444885788020144731526101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57629923858680096487684067 86444885788020144731526101)
    ·
      refine ⟨2026052010656722142145143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 86444885788020144731526101 2026052010656722142145143)
      ·
        refine ⟨3039078015985083213217715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026052010656722142145143 3039078015985083213217715)
        ·
          refine ⟨4558617023977624819826573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039078015985083213217715 4558617023977624819826573)
          ·
            refine ⟨1709481383991609307434965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4558617023977624819826573 1709481383991609307434965)
            ·
              refine ⟨40065969937303343143007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1709481383991609307434965 40065969937303343143007)
              ·
                rfl

theorem cell21_1580071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 7].length) (baseStart_1580071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580071 prefixEnd_1580071 := by exact prefixLift 1580071
  have htrace : WordTrace (prefixWord ++ tailWord_1580071) baseStart_1580071 baseEnd_1580071 := by
    simpa [prefixWord, tailWord_1580071, baseEnd_1580071] using wordTrace_append hprefix tailTrace_1580071
  have hstable : (prefixWord ++ tailWord_1580071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580071).length < 2 ^ (prefixWord ++ tailWord_1580071).sum := by decide
  have hdescent : baseEnd_1580071 < baseStart_1580071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580099 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 4]
def baseStart_1580099 : Nat := 118140960795 + 1580099 * 2 ^ 59
def prefixEnd_1580099 : Nat := 4983230072969 + 3 ^ 40 * 1580099 * 2
def baseEnd_1580099 : Nat := 360600119417208261820339

theorem tailTrace_1580099 : CollatzResearch.WordTrace tailWord_1580099 prefixEnd_1580099 360600119417208261820339 := by
  unfold tailWord_1580099
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630945102578657269703351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38420630068385771513135567 57630945102578657269703351)
  ·
    refine ⟨86446417653867985904555027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57630945102578657269703351 86446417653867985904555027)
    ·
      refine ⟨129669626480801978856832541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86446417653867985904555027 129669626480801978856832541)
      ·
        refine ⟨48626109930300742071312203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129669626480801978856832541 48626109930300742071312203)
        ·
          refine ⟨72939164895451113106968305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48626109930300742071312203 72939164895451113106968305)
          ·
            refine ⟨54704373671588334830226229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72939164895451113106968305 54704373671588334830226229)
            ·
              refine ⟨5128535031711406390333709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54704373671588334830226229 5128535031711406390333709)
              ·
                refine ⟨1923200636891777396375141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5128535031711406390333709 1923200636891777396375141)
                ·
                  refine ⟨360600119417208261820339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923200636891777396375141 360600119417208261820339)
                  ·
                    rfl

theorem cell21_1580099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 4].length) (baseStart_1580099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580099 prefixEnd_1580099 := by exact prefixLift 1580099
  have htrace : WordTrace (prefixWord ++ tailWord_1580099) baseStart_1580099 baseEnd_1580099 := by
    simpa [prefixWord, tailWord_1580099, baseEnd_1580099] using wordTrace_append hprefix tailTrace_1580099
  have hstable : (prefixWord ++ tailWord_1580099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580099).length < 2 ^ (prefixWord ++ tailWord_1580099).sum := by decide
  have hdescent : baseEnd_1580099 < baseStart_1580099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580113 : List Nat := [1, 2, 2, 1, 3, 1, 4, 7]
def baseStart_1580113 : Nat := 118140960795 + 1580113 * 2 ^ 59
def prefixEnd_1580113 : Nat := 4983230072969 + 3 ^ 40 * 1580113 * 2
def baseEnd_1580113 : Nat := 120201104802649116195659

theorem tailTrace_1580113 : CollatzResearch.WordTrace tailWord_1580113 prefixEnd_1580113 120201104802649116195659 := by
  unfold tailWord_1580113
  simp only [CollatzResearch.WordTrace]
  refine ⟨57631455724527937660712993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38420970483018625107141995 57631455724527937660712993)
  ·
    refine ⟨43223591793395953245534745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57631455724527937660712993 43223591793395953245534745)
    ·
      refine ⟨32417693845046964934151059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43223591793395953245534745 32417693845046964934151059)
      ·
        refine ⟨48626540767570447401226589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32417693845046964934151059 48626540767570447401226589)
        ·
          refine ⟨18234952787838917775459971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48626540767570447401226589 18234952787838917775459971)
          ·
            refine ⟨27352429181758376663189957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234952787838917775459971 27352429181758376663189957)
            ·
              refine ⟨5128580471579695624348117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27352429181758376663189957 5128580471579695624348117)
              ·
                refine ⟨120201104802649116195659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5128580471579695624348117 120201104802649116195659)
                ·
                  rfl

theorem cell21_1580113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_1580113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580113 prefixEnd_1580113 := by exact prefixLift 1580113
  have htrace : WordTrace (prefixWord ++ tailWord_1580113) baseStart_1580113 baseEnd_1580113 := by
    simpa [prefixWord, tailWord_1580113, baseEnd_1580113] using wordTrace_append hprefix tailTrace_1580113
  have hstable : (prefixWord ++ tailWord_1580113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580113).length < 2 ^ (prefixWord ++ tailWord_1580113).sum := by decide
  have hdescent : baseEnd_1580113 < baseStart_1580113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580130 : List Nat := [3, 3, 2, 2, 1, 10]
def baseStart_1580130 : Nat := 118140960795 + 1580130 * 2 ^ 59
def prefixEnd_1580130 : Nat := 4983230072969 + 3 ^ 40 * 1580130 * 2
def baseEnd_1580130 : Nat := 13355822001465151733467

theorem tailTrace_1580130 : CollatzResearch.WordTrace tailWord_1580130 prefixEnd_1580130 13355822001465151733467 := by
  unfold tailWord_1580130
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408018941366587391020461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38421383843644233042721229 14408018941366587391020461)
  ·
    refine ⟨5403007103012470271632673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14408018941366587391020461 5403007103012470271632673)
    ·
      refine ⟨4052255327259352703724505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5403007103012470271632673 4052255327259352703724505)
      ·
        refine ⟨3039191495444514527793379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4052255327259352703724505 3039191495444514527793379)
        ·
          refine ⟨4558787243166771791690069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039191495444514527793379 4558787243166771791690069)
          ·
            refine ⟨13355822001465151733467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4558787243166771791690069 13355822001465151733467)
            ·
              rfl

theorem cell21_1580130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 10].length) (baseStart_1580130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580130 prefixEnd_1580130 := by exact prefixLift 1580130
  have htrace : WordTrace (prefixWord ++ tailWord_1580130) baseStart_1580130 baseEnd_1580130 := by
    simpa [prefixWord, tailWord_1580130, baseEnd_1580130] using wordTrace_append hprefix tailTrace_1580130
  have hstable : (prefixWord ++ tailWord_1580130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580130).length < 2 ^ (prefixWord ++ tailWord_1580130).sum := by decide
  have hdescent : baseEnd_1580130 < baseStart_1580130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580144 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_1580144 : Nat := 118140960795 + 1580144 * 2 ^ 59
def prefixEnd_1580144 : Nat := 4983230072969 + 3 ^ 40 * 1580144 * 2
def baseEnd_1580144 : Nat := 360610389030298183570247

theorem tailTrace_1580144 : CollatzResearch.WordTrace tailWord_1580144 prefixEnd_1580144 360610389030298183570247 := by
  unfold tailWord_1580144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816293193707814977545743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38421724258277086636727657 28816293193707814977545743)
  ·
    refine ⟨43224439790561722466318615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28816293193707814977545743 43224439790561722466318615)
    ·
      refine ⟨64836659685842583699477923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43224439790561722466318615 64836659685842583699477923)
      ·
        refine ⟨97254989528763875549216885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64836659685842583699477923 97254989528763875549216885)
        ·
          refine ⟨9117655268321613332739083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97254989528763875549216885 9117655268321613332739083)
          ·
            refine ⟨13676482902482419999108625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117655268321613332739083 13676482902482419999108625)
            ·
              refine ⟨10257362176861814999331469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13676482902482419999108625 10257362176861814999331469)
              ·
                refine ⟨3846510816323180624749301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10257362176861814999331469 3846510816323180624749301)
                ·
                  refine ⟨360610389030298183570247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3846510816323180624749301 360610389030298183570247)
                  ·
                    rfl

theorem cell21_1580144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_1580144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580144 prefixEnd_1580144 := by exact prefixLift 1580144
  have htrace : WordTrace (prefixWord ++ tailWord_1580144) baseStart_1580144 baseEnd_1580144 := by
    simpa [prefixWord, tailWord_1580144, baseEnd_1580144] using wordTrace_append hprefix tailTrace_1580144
  have hstable : (prefixWord ++ tailWord_1580144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580144).length < 2 ^ (prefixWord ++ tailWord_1580144).sum := by decide
  have hdescent : baseEnd_1580144 < baseStart_1580144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580161 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_1580161 : Nat := 118140960795 + 1580161 * 2 ^ 59
def prefixEnd_1580161 : Nat := 4983230072969 + 3 ^ 40 * 1580161 * 2
def baseEnd_1580161 : Nat := 360614268661909931786879

theorem tailTrace_1580161 : CollatzResearch.WordTrace tailWord_1580161 prefixEnd_1580161 360614268661909931786879 := by
  unfold tailWord_1580161
  simp only [CollatzResearch.WordTrace]
  refine ⟨57633206428354041858460337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38422137618902694572306891 57633206428354041858460337)
  ·
    refine ⟨43224904821265531393845253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57633206428354041858460337 43224904821265531393845253)
    ·
      refine ⟨8104669653987287136345985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43224904821265531393845253 8104669653987287136345985)
      ·
        refine ⟨6078502240490465352259489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8104669653987287136345985 6078502240490465352259489)
        ·
          refine ⟨4558876680367849014194617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6078502240490465352259489 4558876680367849014194617)
          ·
            refine ⟨3419157510275886760645963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4558876680367849014194617 3419157510275886760645963)
            ·
              refine ⟨5128736265413830140968945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419157510275886760645963 5128736265413830140968945)
              ·
                refine ⟨3846552199060372605726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128736265413830140968945 3846552199060372605726709)
                ·
                  refine ⟨360614268661909931786879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3846552199060372605726709 360614268661909931786879)
                  ·
                    rfl

theorem cell21_1580161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_1580161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580161 prefixEnd_1580161 := by exact prefixLift 1580161
  have htrace : WordTrace (prefixWord ++ tailWord_1580161) baseStart_1580161 baseEnd_1580161 := by
    simpa [prefixWord, tailWord_1580161, baseEnd_1580161] using wordTrace_append hprefix tailTrace_1580161
  have hstable : (prefixWord ++ tailWord_1580161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580161).length < 2 ^ (prefixWord ++ tailWord_1580161).sum := by decide
  have hdescent : baseEnd_1580161 < baseStart_1580161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580178 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1580178 : Nat := 118140960795 + 1580178 * 2 ^ 59
def prefixEnd_1580178 : Nat := 4983230072969 + 3 ^ 40 * 1580178 * 2
def baseEnd_1580178 : Nat := 360618148293521680003511

theorem tailTrace_1580178 : CollatzResearch.WordTrace tailWord_1580178 prefixEnd_1580178 360618148293521680003511 := by
  unfold tailWord_1580178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408456617323113440457297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38422550979528302507886125 14408456617323113440457297)
  ·
    refine ⟨10806342462992335080342973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14408456617323113440457297 10806342462992335080342973)
    ·
      refine ⟨4052378423622125655128615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10806342462992335080342973 4052378423622125655128615)
      ·
        refine ⟨6078567635433188482692923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052378423622125655128615 6078567635433188482692923)
        ·
          refine ⟨9117851453149782724039385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078567635433188482692923 9117851453149782724039385)
          ·
            refine ⟨6838388589862337043029539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9117851453149782724039385 6838388589862337043029539)
            ·
              refine ⟨10257582884793505564544309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838388589862337043029539 10257582884793505564544309)
              ·
                refine ⟨961648395449391146676029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10257582884793505564544309 961648395449391146676029)
                ·
                  refine ⟨360618148293521680003511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961648395449391146676029 360618148293521680003511)
                  ·
                    rfl

theorem cell21_1580178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1580178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580178 prefixEnd_1580178 := by exact prefixLift 1580178
  have htrace : WordTrace (prefixWord ++ tailWord_1580178) baseStart_1580178 baseEnd_1580178 := by
    simpa [prefixWord, tailWord_1580178, baseEnd_1580178] using wordTrace_append hprefix tailTrace_1580178
  have hstable : (prefixWord ++ tailWord_1580178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580178).length < 2 ^ (prefixWord ++ tailWord_1580178).sum := by decide
  have hdescent : baseEnd_1580178 < baseStart_1580178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580189 : List Nat := [1, 4, 2, 1, 1, 2, 10]
def baseStart_1580189 : Nat := 118140960795 + 1580189 * 2 ^ 59
def prefixEnd_1580189 : Nat := 4983230072969 + 3 ^ 40 * 1580189 * 2
def baseEnd_1580189 : Nat := 40068962071487567257795

theorem tailTrace_1580189 : CollatzResearch.WordTrace tailWord_1580189 prefixEnd_1580189 40068962071487567257795 := by
  unfold tailWord_1580189
  simp only [CollatzResearch.WordTrace]
  refine ⟨57634227672252602640479621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38422818448168401760319747 57634227672252602640479621)
  ·
    refine ⟨10806417688547362995089929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57634227672252602640479621 10806417688547362995089929)
    ·
      refine ⟨8104813266410522246317447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10806417688547362995089929 8104813266410522246317447)
      ·
        refine ⟨12157219899615783369476171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8104813266410522246317447 12157219899615783369476171)
        ·
          refine ⟨18235829849423675054214257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157219899615783369476171 18235829849423675054214257)
          ·
            refine ⟨13676872387067756290660693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18235829849423675054214257 13676872387067756290660693)
            ·
              refine ⟨40068962071487567257795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13676872387067756290660693 40068962071487567257795)
              ·
                rfl

theorem cell21_1580189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 10].length) (baseStart_1580189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580189 prefixEnd_1580189 := by exact prefixLift 1580189
  have htrace : WordTrace (prefixWord ++ tailWord_1580189) baseStart_1580189 baseEnd_1580189 := by
    simpa [prefixWord, tailWord_1580189, baseEnd_1580189] using wordTrace_append hprefix tailTrace_1580189
  have hstable : (prefixWord ++ tailWord_1580189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580189).length < 2 ^ (prefixWord ++ tailWord_1580189).sum := by decide
  have hdescent : baseEnd_1580189 < baseStart_1580189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580209 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 4]
def baseStart_1580209 : Nat := 118140960795 + 1580209 * 2 ^ 59
def prefixEnd_1580209 : Nat := 4983230072969 + 3 ^ 40 * 1580209 * 2
def baseEnd_1580209 : Nat := 360625222915872514986781

theorem tailTrace_1580209 : CollatzResearch.WordTrace tailWord_1580209 prefixEnd_1580209 360625222915872514986781 := by
  unfold tailWord_1580209
  simp only [CollatzResearch.WordTrace]
  refine ⟨57634957132180146056207681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38423304754786764037471787 57634957132180146056207681)
  ·
    refine ⟨43226217849135109542155761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57634957132180146056207681 43226217849135109542155761)
    ·
      refine ⟨32419663386851332156616821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43226217849135109542155761 32419663386851332156616821)
      ·
        refine ⟨3039343442517312389682827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32419663386851332156616821 3039343442517312389682827)
        ·
          refine ⟨4559015163775968584524241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039343442517312389682827 4559015163775968584524241)
          ·
            refine ⟨3419261372831976438393181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4559015163775968584524241 3419261372831976438393181)
            ·
              refine ⟨1282223014811991164397443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3419261372831976438393181 1282223014811991164397443)
              ·
                refine ⟨1923334522217986746596165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282223014811991164397443 1923334522217986746596165)
                ·
                  refine ⟨360625222915872514986781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923334522217986746596165 360625222915872514986781)
                  ·
                    rfl

theorem cell21_1580209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_1580209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580209 prefixEnd_1580209 := by exact prefixLift 1580209
  have htrace : WordTrace (prefixWord ++ tailWord_1580209) baseStart_1580209 baseEnd_1580209 := by
    simpa [prefixWord, tailWord_1580209, baseEnd_1580209] using wordTrace_append hprefix tailTrace_1580209
  have hstable : (prefixWord ++ tailWord_1580209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580209).length < 2 ^ (prefixWord ++ tailWord_1580209).sum := by decide
  have hdescent : baseEnd_1580209 < baseStart_1580209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580268 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1580268 : Nat := 118140960795 + 1580268 * 2 ^ 59
def prefixEnd_1580268 : Nat := 4983230072969 + 3 ^ 40 * 1580268 * 2
def baseEnd_1580268 : Nat := 360638687519701523503327

theorem tailTrace_1580268 : CollatzResearch.WordTrace tailWord_1580268 prefixEnd_1580268 360638687519701523503327 := by
  unfold tailWord_1580268
  simp only [CollatzResearch.WordTrace]
  refine ⟨28818554519483199566302729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38424739359310932755070305 28818554519483199566302729)
  ·
    refine ⟨21613915889612399674727047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28818554519483199566302729 21613915889612399674727047)
    ·
      refine ⟨32420873834418599512090571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21613915889612399674727047 32420873834418599512090571)
      ·
        refine ⟨48631310751627899268135857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32420873834418599512090571 48631310751627899268135857)
        ·
          refine ⟨36473483063720924451101893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48631310751627899268135857 36473483063720924451101893)
          ·
            refine ⟨6838778074447673334581605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36473483063720924451101893 6838778074447673334581605)
            ·
              refine ⟨1282270888958938750234051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6838778074447673334581605 1282270888958938750234051)
              ·
                refine ⟨1923406333438408125351077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282270888958938750234051 1923406333438408125351077)
                ·
                  refine ⟨360638687519701523503327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923406333438408125351077 360638687519701523503327)
                  ·
                    rfl

theorem cell21_1580268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1580268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580268 prefixEnd_1580268 := by exact prefixLift 1580268
  have htrace : WordTrace (prefixWord ++ tailWord_1580268) baseStart_1580268 baseEnd_1580268 := by
    simpa [prefixWord, tailWord_1580268, baseEnd_1580268] using wordTrace_append hprefix tailTrace_1580268
  have hstable : (prefixWord ++ tailWord_1580268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580268).length < 2 ^ (prefixWord ++ tailWord_1580268).sum := by decide
  have hdescent : baseEnd_1580268 < baseStart_1580268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580355 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 9]
def baseStart_1580355 : Nat := 118140960795 + 1580355 * 2 ^ 59
def prefixEnd_1580355 : Nat := 4983230072969 + 3 ^ 40 * 1580355 * 2
def baseEnd_1580355 : Nat := 360658542105008705553149

theorem tailTrace_1580355 : CollatzResearch.WordTrace tailWord_1580355 prefixEnd_1580355 360658542105008705553149 := by
  unfold tailWord_1580355
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640282189651212991022519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38426854793100808660681679 57640282189651212991022519)
  ·
    refine ⟨86460423284476819486533779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57640282189651212991022519 86460423284476819486533779)
    ·
      refine ⟨129690634926715229229800669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86460423284476819486533779 129690634926715229229800669)
      ·
        refine ⟨48633988097518210961175251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129690634926715229229800669 48633988097518210961175251)
        ·
          refine ⟨72950982146277316441762877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48633988097518210961175251 72950982146277316441762877)
          ·
            refine ⟨27356618304853993665661079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72950982146277316441762877 27356618304853993665661079)
            ·
              refine ⟨41034927457280990498491619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356618304853993665661079 41034927457280990498491619)
              ·
                refine ⟨61552391185921485747737429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41034927457280990498491619 61552391185921485747737429)
                ·
                  refine ⟨360658542105008705553149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61552391185921485747737429 360658542105008705553149)
                  ·
                    rfl

theorem cell21_1580355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 9].length) (baseStart_1580355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580355 prefixEnd_1580355 := by exact prefixLift 1580355
  have htrace : WordTrace (prefixWord ++ tailWord_1580355) baseStart_1580355 baseEnd_1580355 := by
    simpa [prefixWord, tailWord_1580355, baseEnd_1580355] using wordTrace_append hprefix tailTrace_1580355
  have hstable : (prefixWord ++ tailWord_1580355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580355).length < 2 ^ (prefixWord ++ tailWord_1580355).sum := by decide
  have hdescent : baseEnd_1580355 < baseStart_1580355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580392 : List Nat := [2, 1, 4, 2, 4, 1, 2, 5]
def baseStart_1580392 : Nat := 118140960795 + 1580392 * 2 ^ 59
def prefixEnd_1580392 : Nat := 4983230072969 + 3 ^ 40 * 1580392 * 2
def baseEnd_1580392 : Nat := 120222328669701621145469

theorem tailTrace_1580392 : CollatzResearch.WordTrace tailWord_1580392 prefixEnd_1580392 120222328669701621145469 := by
  unfold tailWord_1580392
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820815845258584155059715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38427754460344778873412953 28820815845258584155059715)
  ·
    refine ⟨43231223767887876232589573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28820815845258584155059715 43231223767887876232589573)
    ·
      refine ⟨8105854456478976793610545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43231223767887876232589573 8105854456478976793610545)
      ·
        refine ⟨6079390842359232595207909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8105854456478976793610545 6079390842359232595207909)
        ·
          refine ⟨1139885782942356111601483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6079390842359232595207909 1139885782942356111601483)
          ·
            refine ⟨1709828674413534167402225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139885782942356111601483 1709828674413534167402225)
            ·
              refine ⟨1282371505810150625551669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709828674413534167402225 1282371505810150625551669)
              ·
                refine ⟨120222328669701621145469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282371505810150625551669 120222328669701621145469)
                ·
                  rfl

theorem cell21_1580392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_1580392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580392 prefixEnd_1580392 := by exact prefixLift 1580392
  have htrace : WordTrace (prefixWord ++ tailWord_1580392) baseStart_1580392 baseEnd_1580392 := by
    simpa [prefixWord, tailWord_1580392, baseEnd_1580392] using wordTrace_append hprefix tailTrace_1580392
  have hstable : (prefixWord ++ tailWord_1580392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580392).length < 2 ^ (prefixWord ++ tailWord_1580392).sum := by decide
  have hdescent : baseEnd_1580392 < baseStart_1580392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580465 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 3]
def baseStart_1580465 : Nat := 118140960795 + 1580465 * 2 ^ 59
def prefixEnd_1580465 : Nat := 4983230072969 + 3 ^ 40 * 1580465 * 2
def baseEnd_1580465 : Nat := 360683645603672958719591

theorem tailTrace_1580465 : CollatzResearch.WordTrace tailWord_1580465 prefixEnd_1580465 360683645603672958719591 := by
  unfold tailWord_1580465
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644294219252701777526849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38429529479501801185017899 57644294219252701777526849)
  ·
    refine ⟨43233220664439526333145137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57644294219252701777526849 43233220664439526333145137)
    ·
      refine ⟨32424915498329644749858853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43233220664439526333145137 32424915498329644749858853)
      ·
        refine ⟨6079671655936808390598535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32424915498329644749858853 6079671655936808390598535)
        ·
          refine ⟨9119507483905212585897803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079671655936808390598535 9119507483905212585897803)
          ·
            refine ⟨13679261225857818878846705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119507483905212585897803 13679261225857818878846705)
            ·
              refine ⟨10259445919393364159135029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679261225857818878846705 10259445919393364159135029)
              ·
                refine ⟨961823054943127889918909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10259445919393364159135029 961823054943127889918909)
                ·
                  refine ⟨360683645603672958719591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961823054943127889918909 360683645603672958719591)
                  ·
                    rfl

theorem cell21_1580465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 3].length) (baseStart_1580465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580465 prefixEnd_1580465 := by exact prefixLift 1580465
  have htrace : WordTrace (prefixWord ++ tailWord_1580465) baseStart_1580465 baseEnd_1580465 := by
    simpa [prefixWord, tailWord_1580465, baseEnd_1580465] using wordTrace_append hprefix tailTrace_1580465
  have hstable : (prefixWord ++ tailWord_1580465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580465).length < 2 ^ (prefixWord ++ tailWord_1580465).sum := by decide
  have hdescent : baseEnd_1580465 < baseStart_1580465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580538 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1580538 : Nat := 118140960795 + 1580538 * 2 ^ 59
def prefixEnd_1580538 : Nat := 4983230072969 + 3 ^ 40 * 1580538 * 2
def baseEnd_1580538 : Nat := 360700305198241054002775

theorem tailTrace_1580538 : CollatzResearch.WordTrace tailWord_1580538 prefixEnd_1580538 360700305198241054002775 := by
  unfold tailWord_1580538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14411739186997058811233567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38431304498658823496622845 14411739186997058811233567)
  ·
    refine ⟨21617608780495588216850351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14411739186997058811233567 21617608780495588216850351)
    ·
      refine ⟨32426413170743382325275527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21617608780495588216850351 32426413170743382325275527)
      ·
        refine ⟨48639619756115073487913291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32426413170743382325275527 48639619756115073487913291)
        ·
          refine ⟨72959429634172610231869937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48639619756115073487913291 72959429634172610231869937)
          ·
            refine ⟨54719572225629457673902453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72959429634172610231869937 54719572225629457673902453)
            ·
              refine ⟨5129959896152761656928355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54719572225629457673902453 5129959896152761656928355)
              ·
                refine ⟨7694939844229142485392533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129959896152761656928355 7694939844229142485392533)
                ·
                  refine ⟨360700305198241054002775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7694939844229142485392533 360700305198241054002775)
                  ·
                    rfl

theorem cell21_1580538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1580538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580538 prefixEnd_1580538 := by exact prefixLift 1580538
  have htrace : WordTrace (prefixWord ++ tailWord_1580538) baseStart_1580538 baseEnd_1580538 := by
    simpa [prefixWord, tailWord_1580538, baseEnd_1580538] using wordTrace_append hprefix tailTrace_1580538
  have hstable : (prefixWord ++ tailWord_1580538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580538).length < 2 ^ (prefixWord ++ tailWord_1580538).sum := by decide
  have hdescent : baseEnd_1580538 < baseStart_1580538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580541 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 3]
def baseStart_1580541 : Nat := 118140960795 + 1580541 * 2 ^ 59
def prefixEnd_1580541 : Nat := 4983230072969 + 3 ^ 40 * 1580541 * 2
def baseEnd_1580541 : Nat := 360700989839113715452769

theorem tailTrace_1580541 : CollatzResearch.WordTrace tailWord_1580541 prefixEnd_1580541 360700989839113715452769 := by
  unfold tailWord_1580541
  simp only [CollatzResearch.WordTrace]
  refine ⟨57647066166977366757293477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38431377444651577838195651 57647066166977366757293477)
  ·
    refine ⟨10808824906308256266992527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57647066166977366757293477 10808824906308256266992527)
    ·
      refine ⟨16213237359462384400488791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808824906308256266992527 16213237359462384400488791)
      ·
        refine ⟨24319856039193576600733187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16213237359462384400488791 24319856039193576600733187)
        ·
          refine ⟨36479784058790364901099781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24319856039193576600733187 36479784058790364901099781)
          ·
            refine ⟨6839959511023193418956209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36479784058790364901099781 6839959511023193418956209)
            ·
              refine ⟨5129969633267395064217157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6839959511023193418956209 5129969633267395064217157)
              ·
                refine ⟨961869306237636574540717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5129969633267395064217157 961869306237636574540717)
                ·
                  refine ⟨360700989839113715452769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961869306237636574540717 360700989839113715452769)
                  ·
                    rfl

theorem cell21_1580541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_1580541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580541 prefixEnd_1580541 := by exact prefixLift 1580541
  have htrace : WordTrace (prefixWord ++ tailWord_1580541) baseStart_1580541 baseEnd_1580541 := by
    simpa [prefixWord, tailWord_1580541, baseEnd_1580541] using wordTrace_append hprefix tailTrace_1580541
  have hstable : (prefixWord ++ tailWord_1580541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580541).length < 2 ^ (prefixWord ++ tailWord_1580541).sum := by decide
  have hdescent : baseEnd_1580541 < baseStart_1580541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580600 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_1580600 : Nat := 118140960795 + 1580600 * 2 ^ 59
def prefixEnd_1580600 : Nat := 4983230072969 + 3 ^ 40 * 1580600 * 2
def baseEnd_1580600 : Nat := 360714454442942723969315

theorem tailTrace_1580600 : CollatzResearch.WordTrace tailWord_1580600 prefixEnd_1580600 360714454442942723969315 := by
  unfold tailWord_1580600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28824609036881809916845627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38432812049175746555794169 28824609036881809916845627)
  ·
    refine ⟨43236913555322714875268441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28824609036881809916845627 43236913555322714875268441)
    ·
      refine ⟨32427685166492036156451331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43236913555322714875268441 32427685166492036156451331)
      ·
        refine ⟨48641527749738054234676997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32427685166492036156451331 48641527749738054234676997)
        ·
          refine ⟨9120286453075885169001937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48641527749738054234676997 9120286453075885169001937)
          ·
            refine ⟨6840214839806913876751453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9120286453075885169001937 6840214839806913876751453)
            ·
              refine ⟨2565080564927592703781795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6840214839806913876751453 2565080564927592703781795)
              ·
                refine ⟨3847620847391389055672693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565080564927592703781795 3847620847391389055672693)
                ·
                  refine ⟨360714454442942723969315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3847620847391389055672693 360714454442942723969315)
                  ·
                    rfl

theorem cell21_1580600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_1580600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580600 prefixEnd_1580600 := by exact prefixLift 1580600
  have htrace : WordTrace (prefixWord ++ tailWord_1580600) baseStart_1580600 baseEnd_1580600 := by
    simpa [prefixWord, tailWord_1580600, baseEnd_1580600] using wordTrace_append hprefix tailTrace_1580600
  have hstable : (prefixWord ++ tailWord_1580600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580600).length < 2 ^ (prefixWord ++ tailWord_1580600).sum := by decide
  have hdescent : baseEnd_1580600 < baseStart_1580600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580648 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_1580648 : Nat := 118140960795 + 1580648 * 2 ^ 59
def prefixEnd_1580648 : Nat := 4983230072969 + 3 ^ 40 * 1580648 * 2
def baseEnd_1580648 : Nat := 360725408696905307169217

theorem tailTrace_1580648 : CollatzResearch.WordTrace tailWord_1580648 prefixEnd_1580648 360725408696905307169217 := by
  unfold tailWord_1580648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28825484388794862015719299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38433979185059816020959065 28825484388794862015719299)
  ·
    refine ⟨43238226583192293023578949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28825484388794862015719299 43238226583192293023578949)
    ·
      refine ⟨8107167484348554941921053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43238226583192293023578949 8107167484348554941921053)
      ·
        refine ⟨3040187806630708103220395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8107167484348554941921053 3040187806630708103220395)
        ·
          refine ⟨4560281709946062154830593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040187806630708103220395 4560281709946062154830593)
          ·
            refine ⟨3420211282459546616122945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560281709946062154830593 3420211282459546616122945)
            ·
              refine ⟨2565158461844659962092209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420211282459546616122945 2565158461844659962092209)
              ·
                refine ⟨1923868846383494971569157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565158461844659962092209 1923868846383494971569157)
                ·
                  refine ⟨360725408696905307169217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1923868846383494971569157 360725408696905307169217)
                  ·
                    rfl

theorem cell21_1580648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_1580648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580648 prefixEnd_1580648 := by exact prefixLift 1580648
  have htrace : WordTrace (prefixWord ++ tailWord_1580648) baseStart_1580648 baseEnd_1580648 := by
    simpa [prefixWord, tailWord_1580648, baseEnd_1580648] using wordTrace_append hprefix tailTrace_1580648
  have hstable : (prefixWord ++ tailWord_1580648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580648).length < 2 ^ (prefixWord ++ tailWord_1580648).sum := by decide
  have hdescent : baseEnd_1580648 < baseStart_1580648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580662 : List Nat := [5, 1, 1, 2, 2, 1, 3, 6]
def baseStart_1580662 : Nat := 118140960795 + 1580662 * 2 ^ 59
def prefixEnd_1580662 : Nat := 4983230072969 + 3 ^ 40 * 1580662 * 2
def baseEnd_1580662 : Nat := 120242867895881464645285

theorem tailTrace_1580662 : CollatzResearch.WordTrace tailWord_1580662 prefixEnd_1580662 120242867895881464645285 := by
  unfold tailWord_1580662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603217462471187776403015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38434319599692669614965493 3603217462471187776403015)
  ·
    refine ⟨5404826193706781664604523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603217462471187776403015 5404826193706781664604523)
    ·
      refine ⟨8107239290560172496906785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404826193706781664604523 8107239290560172496906785)
      ·
        refine ⟨6080429467920129372680089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8107239290560172496906785 6080429467920129372680089)
        ·
          refine ⟨4560322100940097029510067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080429467920129372680089 4560322100940097029510067)
          ·
            refine ⟨6840483151410145544265101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560322100940097029510067 6840483151410145544265101)
            ·
              refine ⟨2565181181778804579099413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6840483151410145544265101 2565181181778804579099413)
              ·
                refine ⟨120242867895881464645285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2565181181778804579099413 120242867895881464645285)
                ·
                  rfl

theorem cell21_1580662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_1580662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580662 prefixEnd_1580662 := by exact prefixLift 1580662
  have htrace : WordTrace (prefixWord ++ tailWord_1580662) baseStart_1580662 baseEnd_1580662 := by
    simpa [prefixWord, tailWord_1580662, baseEnd_1580662] using wordTrace_append hprefix tailTrace_1580662
  have hstable : (prefixWord ++ tailWord_1580662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580662).length < 2 ^ (prefixWord ++ tailWord_1580662).sum := by decide
  have hdescent : baseEnd_1580662 < baseStart_1580662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580735 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 5]
def baseStart_1580735 : Nat := 118140960795 + 1580735 * 2 ^ 59
def prefixEnd_1580735 : Nat := 4983230072969 + 3 ^ 40 * 1580735 * 2
def baseEnd_1580735 : Nat := 360745263282212489219039

theorem tailTrace_1580735 : CollatzResearch.WordTrace tailWord_1580735 prefixEnd_1580735 360745263282212489219039 := by
  unfold tailWord_1580735
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654141928274537889855659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38436094618849691926570439 57654141928274537889855659)
  ·
    refine ⟨86481212892411806834783489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57654141928274537889855659 86481212892411806834783489)
    ·
      refine ⟨64860909669308855126087617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86481212892411806834783489 64860909669308855126087617)
      ·
        refine ⟨48645682251981641344565713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64860909669308855126087617 48645682251981641344565713)
        ·
          refine ⟨36484261688986231008424285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48645682251981641344565713 36484261688986231008424285)
          ·
            refine ⟨13681598133369836628159107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36484261688986231008424285 13681598133369836628159107)
            ·
              refine ⟨20522397200054754942238661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13681598133369836628159107 20522397200054754942238661)
              ·
                refine ⟨3847949475010266551669749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20522397200054754942238661 3847949475010266551669749)
                ·
                  refine ⟨360745263282212489219039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3847949475010266551669749 360745263282212489219039)
                  ·
                    rfl

theorem cell21_1580735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 5].length) (baseStart_1580735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580735 prefixEnd_1580735 := by exact prefixLift 1580735
  have htrace : WordTrace (prefixWord ++ tailWord_1580735) baseStart_1580735 baseEnd_1580735 := by
    simpa [prefixWord, tailWord_1580735, baseEnd_1580735] using wordTrace_append hprefix tailTrace_1580735
  have hstable : (prefixWord ++ tailWord_1580735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580735).length < 2 ^ (prefixWord ++ tailWord_1580735).sum := by decide
  have hdescent : baseEnd_1580735 < baseStart_1580735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580752 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_1580752 : Nat := 118140960795 + 1580752 * 2 ^ 59
def prefixEnd_1580752 : Nat := 4983230072969 + 3 ^ 40 * 1580752 * 2
def baseEnd_1580752 : Nat := 360749142913824237435671

theorem tailTrace_1580752 : CollatzResearch.WordTrace tailWord_1580752 prefixEnd_1580752 360749142913824237435671 := by
  unfold tailWord_1580752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28827380984606474896612255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38436507979475299862149673 28827380984606474896612255)
  ·
    refine ⟨43241071476909712344918383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28827380984606474896612255 43241071476909712344918383)
    ·
      refine ⟨64861607215364568517377575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43241071476909712344918383 64861607215364568517377575)
      ·
        refine ⟨97292410823046852776066363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64861607215364568517377575 97292410823046852776066363)
        ·
          refine ⟨145938616234570279164099545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97292410823046852776066363 145938616234570279164099545)
          ·
            refine ⟨109453962175927709373074659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145938616234570279164099545 109453962175927709373074659)
            ·
              refine ⟨164180943263891564059611989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109453962175927709373074659 164180943263891564059611989)
              ·
                refine ⟨961997714436864633161789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 164180943263891564059611989 961997714436864633161789)
                ·
                  refine ⟨360749142913824237435671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 961997714436864633161789 360749142913824237435671)
                  ·
                    rfl

theorem cell21_1580752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_1580752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580752 prefixEnd_1580752 := by exact prefixLift 1580752
  have htrace : WordTrace (prefixWord ++ tailWord_1580752) baseStart_1580752 baseEnd_1580752 := by
    simpa [prefixWord, tailWord_1580752, baseEnd_1580752] using wordTrace_append hprefix tailTrace_1580752
  have hstable : (prefixWord ++ tailWord_1580752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580752).length < 2 ^ (prefixWord ++ tailWord_1580752).sum := by decide
  have hdescent : baseEnd_1580752 < baseStart_1580752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580769 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 5]
def baseStart_1580769 : Nat := 118140960795 + 1580769 * 2 ^ 59
def prefixEnd_1580769 : Nat := 4983230072969 + 3 ^ 40 * 1580769 * 2
def baseEnd_1580769 : Nat := 360753022545435985652303

theorem tailTrace_1580769 : CollatzResearch.WordTrace tailWord_1580769 prefixEnd_1580769 360753022545435985652303 := by
  unfold tailWord_1580769
  simp only [CollatzResearch.WordTrace]
  refine ⟨57655382010151361696593361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38436921340100907797728907 57655382010151361696593361)
  ·
    refine ⟨43241536507613521272445021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57655382010151361696593361 43241536507613521272445021)
    ·
      refine ⟨16215576190355070477166883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43241536507613521272445021 16215576190355070477166883)
      ·
        refine ⟨24323364285532605715750325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16215576190355070477166883 24323364285532605715750325)
        ·
          refine ⟨2280315401768681785851593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24323364285532605715750325 2280315401768681785851593)
          ·
            refine ⟨1710236551326511339388695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280315401768681785851593 1710236551326511339388695)
            ·
              refine ⟨2565354826989767009083043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710236551326511339388695 2565354826989767009083043)
              ·
                refine ⟨3848032240484650513624565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565354826989767009083043 3848032240484650513624565)
                ·
                  refine ⟨360753022545435985652303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848032240484650513624565 360753022545435985652303)
                  ·
                    rfl

theorem cell21_1580769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 5].length) (baseStart_1580769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580769 prefixEnd_1580769 := by exact prefixLift 1580769
  have htrace : WordTrace (prefixWord ++ tailWord_1580769) baseStart_1580769 baseEnd_1580769 := by
    simpa [prefixWord, tailWord_1580769, baseEnd_1580769] using wordTrace_append hprefix tailTrace_1580769
  have hstable : (prefixWord ++ tailWord_1580769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580769).length < 2 ^ (prefixWord ++ tailWord_1580769).sum := by decide
  have hdescent : baseEnd_1580769 < baseStart_1580769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580780 : List Nat := [2, 2, 1, 1, 2, 2, 3, 8]
def baseStart_1580780 : Nat := 118140960795 + 1580780 * 2 ^ 59
def prefixEnd_1580780 : Nat := 4983230072969 + 3 ^ 40 * 1580780 * 2
def baseEnd_1580780 : Nat := 120251844298434136989649

theorem tailTrace_1580780 : CollatzResearch.WordTrace tailWord_1580780 prefixEnd_1580780 120251844298434136989649 := by
  unfold tailWord_1580780
  simp only [CollatzResearch.WordTrace]
  refine ⟨28827891606555755287621897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38437188808741007050162529 28827891606555755287621897)
  ·
    refine ⟨21620918704916816465716423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28827891606555755287621897 21620918704916816465716423)
    ·
      refine ⟨32431378057375224698574635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21620918704916816465716423 32431378057375224698574635)
      ·
        refine ⟨48647067086062837047861953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32431378057375224698574635 48647067086062837047861953)
        ·
          refine ⟨36485300314547127785896465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48647067086062837047861953 36485300314547127785896465)
          ·
            refine ⟨27363975235910345839422349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36485300314547127785896465 27363975235910345839422349)
            ·
              refine ⟨10261490713466379689783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27363975235910345839422349 10261490713466379689783381)
              ·
                refine ⟨120251844298434136989649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10261490713466379689783381 120251844298434136989649)
                ·
                  rfl

theorem cell21_1580780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_1580780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580780 prefixEnd_1580780 := by exact prefixLift 1580780
  have htrace : WordTrace (prefixWord ++ tailWord_1580780) baseStart_1580780 baseEnd_1580780 := by
    simpa [prefixWord, tailWord_1580780, baseEnd_1580780] using wordTrace_append hprefix tailTrace_1580780
  have hstable : (prefixWord ++ tailWord_1580780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580780).length < 2 ^ (prefixWord ++ tailWord_1580780).sum := by decide
  have hdescent : baseEnd_1580780 < baseStart_1580780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580820 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1580820 : Nat := 118140960795 + 1580820 * 2 ^ 59
def prefixEnd_1580820 : Nat := 4983230072969 + 3 ^ 40 * 1580820 * 2
def baseEnd_1580820 : Nat := 360764661440271230302199

theorem tailTrace_1580820 : CollatzResearch.WordTrace tailWord_1580820 prefixEnd_1580820 360764661440271230302199 := by
  unfold tailWord_1580820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828621066483298703349957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38438161421977731604466609 28828621066483298703349957)
  ·
    refine ⟨5405366449965618506878117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28828621066483298703349957 5405366449965618506878117)
    ·
      refine ⟨1013506209368553470039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5405366449965618506878117 1013506209368553470039647)
      ·
        refine ⟨1520259314052830205059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013506209368553470039647 1520259314052830205059471)
        ·
          refine ⟨2280388971079245307589207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520259314052830205059471 2280388971079245307589207)
          ·
            refine ⟨3420583456618867961383811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280388971079245307589207 3420583456618867961383811)
            ·
              refine ⟨5130875184928301942075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420583456618867961383811 5130875184928301942075717)
              ·
                refine ⟨962039097174056614139197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5130875184928301942075717 962039097174056614139197)
                ·
                  refine ⟨360764661440271230302199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962039097174056614139197 360764661440271230302199)
                  ·
                    rfl

theorem cell21_1580820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1580820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580820 prefixEnd_1580820 := by exact prefixLift 1580820
  have htrace : WordTrace (prefixWord ++ tailWord_1580820) baseStart_1580820 baseEnd_1580820 := by
    simpa [prefixWord, tailWord_1580820, baseEnd_1580820] using wordTrace_append hprefix tailTrace_1580820
  have hstable : (prefixWord ++ tailWord_1580820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580820).length < 2 ^ (prefixWord ++ tailWord_1580820).sum := by decide
  have hdescent : baseEnd_1580820 < baseStart_1580820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580825 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 10]
def baseStart_1580825 : Nat := 118140960795 + 1580825 * 2 ^ 59
def prefixEnd_1580825 : Nat := 4983230072969 + 3 ^ 40 * 1580825 * 2
def baseEnd_1580825 : Nat := 360765802508392332718855

theorem tailTrace_1580825 : CollatzResearch.WordTrace tailWord_1580825 prefixEnd_1580825 360765802508392332718855 := by
  unfold tailWord_1580825
  simp only [CollatzResearch.WordTrace]
  refine ⟨57657424497948483260631929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38438282998632322173754619 57657424497948483260631929)
  ·
    refine ⟨43243068373461362445473947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57657424497948483260631929 43243068373461362445473947)
    ·
      refine ⟨64864602560192043668210921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43243068373461362445473947 64864602560192043668210921)
      ·
        refine ⟨48648451920144032751158191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64864602560192043668210921 48648451920144032751158191)
        ·
          refine ⟨72972677880216049126737287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48648451920144032751158191 72972677880216049126737287)
          ·
            refine ⟨109459016820324073690105931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72972677880216049126737287 109459016820324073690105931)
            ·
              refine ⟨164188525230486110535158897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109459016820324073690105931 164188525230486110535158897)
              ·
                refine ⟨123141393922864582901369173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164188525230486110535158897 123141393922864582901369173)
                ·
                  refine ⟨360765802508392332718855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123141393922864582901369173 360765802508392332718855)
                  ·
                    rfl

theorem cell21_1580825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_1580825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580825 prefixEnd_1580825 := by exact prefixLift 1580825
  have htrace : WordTrace (prefixWord ++ tailWord_1580825) baseStart_1580825 baseEnd_1580825 := by
    simpa [prefixWord, tailWord_1580825, baseEnd_1580825] using wordTrace_append hprefix tailTrace_1580825
  have hstable : (prefixWord ++ tailWord_1580825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580825).length < 2 ^ (prefixWord ++ tailWord_1580825).sum := by decide
  have hdescent : baseEnd_1580825 < baseStart_1580825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580862 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1580862 : Nat := 118140960795 + 1580862 * 2 ^ 59
def prefixEnd_1580862 : Nat := 4983230072969 + 3 ^ 40 * 1580862 * 2
def baseEnd_1580862 : Nat := 360774246412488490602113

theorem tailTrace_1580862 : CollatzResearch.WordTrace tailWord_1580862 prefixEnd_1580862 360774246412488490602113 := by
  unfold tailWord_1580862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207346749851804822466105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38439182665876292386485893 7207346749851804822466105)
  ·
    refine ⟨5405510062388853616849579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7207346749851804822466105 5405510062388853616849579)
    ·
      refine ⟨8108265093583280425274369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405510062388853616849579 8108265093583280425274369)
      ·
        refine ⟨6081198820187460318955777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108265093583280425274369 6081198820187460318955777)
        ·
          refine ⟨4560899115140595239216833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6081198820187460318955777 4560899115140595239216833)
          ·
            refine ⟨3420674336355446429412625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560899115140595239216833 3420674336355446429412625)
            ·
              refine ⟨2565505752266584822059469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420674336355446429412625 2565505752266584822059469)
              ·
                refine ⟨962064657099969308272301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565505752266584822059469 962064657099969308272301)
                ·
                  refine ⟨360774246412488490602113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962064657099969308272301 360774246412488490602113)
                  ·
                    rfl

theorem cell21_1580862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1580862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580862 prefixEnd_1580862 := by exact prefixLift 1580862
  have htrace : WordTrace (prefixWord ++ tailWord_1580862) baseStart_1580862 baseEnd_1580862 := by
    simpa [prefixWord, tailWord_1580862, baseEnd_1580862] using wordTrace_append hprefix tailTrace_1580862
  have hstable : (prefixWord ++ tailWord_1580862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580862).length < 2 ^ (prefixWord ++ tailWord_1580862).sum := by decide
  have hdescent : baseEnd_1580862 < baseStart_1580862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580876 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1580876 : Nat := 118140960795 + 1580876 * 2 ^ 59
def prefixEnd_1580876 : Nat := 4983230072969 + 3 ^ 40 * 1580876 * 2
def baseEnd_1580876 : Nat := 360777441403227577368751

theorem tailTrace_1580876 : CollatzResearch.WordTrace tailWord_1580876 prefixEnd_1580876 360777441403227577368751 := by
  unfold tailWord_1580876
  simp only [CollatzResearch.WordTrace]
  refine ⟨28829642310381859485369241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38439523080509145980492321 28829642310381859485369241)
  ·
    refine ⟨21622231732786394614026931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28829642310381859485369241 21622231732786394614026931)
    ·
      refine ⟨32433347599179591921040397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21622231732786394614026931 32433347599179591921040397)
      ·
        refine ⟨12162505349692346970390149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32433347599179591921040397 12162505349692346970390149)
        ·
          refine ⟨2280469753067315056948153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12162505349692346970390149 2280469753067315056948153)
          ·
            refine ⟨1710352314800486292711115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280469753067315056948153 1710352314800486292711115)
            ·
              refine ⟨2565528472200729439066673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710352314800486292711115 2565528472200729439066673)
              ·
                refine ⟨1924146354150547079300005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565528472200729439066673 1924146354150547079300005)
                ·
                  refine ⟨360777441403227577368751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924146354150547079300005 360777441403227577368751)
                  ·
                    rfl

theorem cell21_1580876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1580876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580876 prefixEnd_1580876 := by exact prefixLift 1580876
  have htrace : WordTrace (prefixWord ++ tailWord_1580876) baseStart_1580876 baseEnd_1580876 := by
    simpa [prefixWord, tailWord_1580876, baseEnd_1580876] using wordTrace_append hprefix tailTrace_1580876
  have hstable : (prefixWord ++ tailWord_1580876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580876).length < 2 ^ (prefixWord ++ tailWord_1580876).sum := by decide
  have hdescent : baseEnd_1580876 < baseStart_1580876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580932 : List Nat := [2, 3, 2, 1, 1, 1, 11]
def baseStart_1580932 : Nat := 118140960795 + 1580932 * 2 ^ 59
def prefixEnd_1580932 : Nat := 4983230072969 + 3 ^ 40 * 1580932 * 2
def baseEnd_1580932 : Nat := 40087802374020436048367

theorem tailTrace_1580932 : CollatzResearch.WordTrace tailWord_1580932 prefixEnd_1580932 40087802374020436048367 := by
  unfold tailWord_1580932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28830663554280420267388525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38440884739040560356518033 28830663554280420267388525)
  ·
    refine ⟨10811498832855157600270697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28830663554280420267388525 10811498832855157600270697)
    ·
      refine ⟨8108624124641368200203023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10811498832855157600270697 8108624124641368200203023)
      ·
        refine ⟨12162936186962052300304535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108624124641368200203023 12162936186962052300304535)
        ·
          refine ⟨18244404280443078450456803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12162936186962052300304535 18244404280443078450456803)
          ·
            refine ⟨27366606420664617675685205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18244404280443078450456803 27366606420664617675685205)
            ·
              refine ⟨40087802374020436048367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27366606420664617675685205 40087802374020436048367)
              ·
                rfl

theorem cell21_1580932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 11].length) (baseStart_1580932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580932 prefixEnd_1580932 := by exact prefixLift 1580932
  have htrace : WordTrace (prefixWord ++ tailWord_1580932) baseStart_1580932 baseEnd_1580932 := by
    simpa [prefixWord, tailWord_1580932, baseEnd_1580932] using wordTrace_append hprefix tailTrace_1580932
  have hstable : (prefixWord ++ tailWord_1580932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580932).length < 2 ^ (prefixWord ++ tailWord_1580932).sum := by decide
  have hdescent : baseEnd_1580932 < baseStart_1580932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580938 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_1580938 : Nat := 118140960795 + 1580938 * 2 ^ 59
def prefixEnd_1580938 : Nat := 4983230072969 + 3 ^ 40 * 1580938 * 2
def baseEnd_1580938 : Nat := 360791590647929247335291

theorem tailTrace_1580938 : CollatzResearch.WordTrace tailWord_1580938 prefixEnd_1580938 360791590647929247335291 := by
  unfold tailWord_1580938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415386486634775889873867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38441030631026069039663645 14415386486634775889873867)
  ·
    refine ⟨21623079729952163834810801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14415386486634775889873867 21623079729952163834810801)
    ·
      refine ⟨16217309797464122876108101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21623079729952163834810801 16217309797464122876108101)
      ·
        refine ⟨3040745587024523039270269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16217309797464122876108101 3040745587024523039270269)
        ·
          refine ⟨1140279595134196139726351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3040745587024523039270269 1140279595134196139726351)
          ·
            refine ⟨1710419392701294209589527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140279595134196139726351 1710419392701294209589527)
            ·
              refine ⟨2565629089051941314384291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710419392701294209589527 2565629089051941314384291)
              ·
                refine ⟨3848443633577911971576437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565629089051941314384291 3848443633577911971576437)
                ·
                  refine ⟨360791590647929247335291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3848443633577911971576437 360791590647929247335291)
                  ·
                    rfl

theorem cell21_1580938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_1580938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580938 prefixEnd_1580938 := by exact prefixLift 1580938
  have htrace : WordTrace (prefixWord ++ tailWord_1580938) baseStart_1580938 baseEnd_1580938 := by
    simpa [prefixWord, tailWord_1580938, baseEnd_1580938] using wordTrace_append hprefix tailTrace_1580938
  have hstable : (prefixWord ++ tailWord_1580938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580938).length < 2 ^ (prefixWord ++ tailWord_1580938).sum := by decide
  have hdescent : baseEnd_1580938 < baseStart_1580938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1580952 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_1580952 : Nat := 118140960795 + 1580952 * 2 ^ 59
def prefixEnd_1580952 : Nat := 4983230072969 + 3 ^ 40 * 1580952 * 2
def baseEnd_1580952 : Nat := 360794785638668334101929

theorem tailTrace_1580952 : CollatzResearch.WordTrace tailWord_1580952 prefixEnd_1580952 360794785638668334101929 := by
  unfold tailWord_1580952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28831028284244191975252555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38441371045658922633670073 28831028284244191975252555)
  ·
    refine ⟨43246542426366287962878833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28831028284244191975252555 43246542426366287962878833)
    ·
      refine ⟨32434906819774715972159125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43246542426366287962878833 32434906819774715972159125)
      ·
        refine ⟨1520386257176939811194959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32434906819774715972159125 1520386257176939811194959)
        ·
          refine ⟨2280579385765409716792439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520386257176939811194959 2280579385765409716792439)
          ·
            refine ⟨3420869078648114575188659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280579385765409716792439 3420869078648114575188659)
            ·
              refine ⟨5131303617972171862782989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420869078648114575188659 5131303617972171862782989)
              ·
                refine ⟨1924238856739564448543621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5131303617972171862782989 1924238856739564448543621)
                ·
                  refine ⟨360794785638668334101929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924238856739564448543621 360794785638668334101929)
                  ·
                    rfl

theorem cell21_1580952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_1580952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1580952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1580952 prefixEnd_1580952 := by exact prefixLift 1580952
  have htrace : WordTrace (prefixWord ++ tailWord_1580952) baseStart_1580952 baseEnd_1580952 := by
    simpa [prefixWord, tailWord_1580952, baseEnd_1580952] using wordTrace_append hprefix tailTrace_1580952
  have hstable : (prefixWord ++ tailWord_1580952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1580952).length < 2 ^ (prefixWord ++ tailWord_1580952).sum := by decide
  have hdescent : baseEnd_1580952 < baseStart_1580952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1580952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581008 : List Nat := [2, 1, 1, 1, 1, 2, 7, 6]
def baseStart_1581008 : Nat := 118140960795 + 1581008 * 2 ^ 59
def prefixEnd_1581008 : Nat := 4983230072969 + 3 ^ 40 * 1581008 * 2
def baseEnd_1581008 : Nat := 120269188533874893722827

theorem tailTrace_1581008 : CollatzResearch.WordTrace tailWord_1581008 prefixEnd_1581008 120269188533874893722827 := by
  unfold tailWord_1581008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28832049528142752757271839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38442732704190337009695785 28832049528142752757271839)
  ·
    refine ⟨43248074292214129135907759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28832049528142752757271839 43248074292214129135907759)
    ·
      refine ⟨64872111438321193703861639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43248074292214129135907759 64872111438321193703861639)
      ·
        refine ⟨97308167157481790555792459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64872111438321193703861639 97308167157481790555792459)
        ·
          refine ⟨145962250736222685833688689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97308167157481790555792459 145962250736222685833688689)
          ·
            refine ⟨109471688052167014375266517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145962250736222685833688689 109471688052167014375266517)
            ·
              refine ⟨2565742688722664399420309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109471688052167014375266517 2565742688722664399420309)
              ·
                refine ⟨120269188533874893722827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2565742688722664399420309 120269188533874893722827)
                ·
                  rfl

theorem cell21_1581008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_1581008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581008 prefixEnd_1581008 := by exact prefixLift 1581008
  have htrace : WordTrace (prefixWord ++ tailWord_1581008) baseStart_1581008 baseEnd_1581008 := by
    simpa [prefixWord, tailWord_1581008, baseEnd_1581008] using wordTrace_append hprefix tailTrace_1581008
  have hstable : (prefixWord ++ tailWord_1581008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581008).length < 2 ^ (prefixWord ++ tailWord_1581008).sum := by decide
  have hdescent : baseEnd_1581008 < baseStart_1581008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581076 : List Nat := [2, 4, 3, 2, 1, 2, 2, 5]
def baseStart_1581076 : Nat := 118140960795 + 1581076 * 2 ^ 59
def prefixEnd_1581076 : Nat := 4983230072969 + 3 ^ 40 * 1581076 * 2
def baseEnd_1581076 : Nat := 120274361376023891345003

theorem tailTrace_1581076 : CollatzResearch.WordTrace tailWord_1581076 prefixEnd_1581076 120274361376023891345003 := by
  unfold tailWord_1581076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833289610019576564009541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38444386146692768752012721 28833289610019576564009541)
  ·
    refine ⟨5406241801878670605751789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28833289610019576564009541 5406241801878670605751789)
    ·
      refine ⟨2027340675704501477156921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5406241801878670605751789 2027340675704501477156921)
      ·
        refine ⟨1520505506778376107867691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027340675704501477156921 1520505506778376107867691)
        ·
          refine ⟨2280758260167564161801537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520505506778376107867691 2280758260167564161801537)
          ·
            refine ⟨1710568695125673121351153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2280758260167564161801537 1710568695125673121351153)
            ·
              refine ⟨1282926521344254841013365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1710568695125673121351153 1282926521344254841013365)
              ·
                refine ⟨120274361376023891345003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1282926521344254841013365 120274361376023891345003)
                ·
                  rfl

theorem cell21_1581076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_1581076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581076 prefixEnd_1581076 := by exact prefixLift 1581076
  have htrace : WordTrace (prefixWord ++ tailWord_1581076) baseStart_1581076 baseEnd_1581076 := by
    simpa [prefixWord, tailWord_1581076, baseEnd_1581076] using wordTrace_append hprefix tailTrace_1581076
  have hstable : (prefixWord ++ tailWord_1581076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581076).length < 2 ^ (prefixWord ++ tailWord_1581076).sum := by decide
  have hdescent : baseEnd_1581076 < baseStart_1581076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581118 : List Nat := [4, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1581118 : Nat := 118140960795 + 1581118 * 2 ^ 59
def prefixEnd_1581118 : Nat := 4983230072969 + 3 ^ 40 * 1581118 * 2
def baseEnd_1581118 : Nat := 120277556366762978111641

theorem tailTrace_1581118 : CollatzResearch.WordTrace tailWord_1581118 prefixEnd_1581118 120277556366762978111641 := by
  unfold tailWord_1581118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208513885735874287631001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38445407390591329534032005 7208513885735874287631001)
  ·
    refine ⟨5406385414301905715723251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7208513885735874287631001 5406385414301905715723251)
    ·
      refine ⟨8109578121452858573584877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406385414301905715723251 8109578121452858573584877)
      ·
        refine ⟨3041091795544821965094329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8109578121452858573584877 3041091795544821965094329)
        ·
          refine ⟨2280818846658616473820747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041091795544821965094329 2280818846658616473820747)
          ·
            refine ⟨3421228269987924710731121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280818846658616473820747 3421228269987924710731121)
            ·
              refine ⟨2565921202490943533048341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421228269987924710731121 2565921202490943533048341)
              ·
                refine ⟨120277556366762978111641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2565921202490943533048341 120277556366762978111641)
                ·
                  rfl

theorem cell21_1581118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1581118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581118 prefixEnd_1581118 := by exact prefixLift 1581118
  have htrace : WordTrace (prefixWord ++ tailWord_1581118) baseStart_1581118 baseEnd_1581118 := by
    simpa [prefixWord, tailWord_1581118, baseEnd_1581118] using wordTrace_append hprefix tailTrace_1581118
  have hstable : (prefixWord ++ tailWord_1581118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581118).length < 2 ^ (prefixWord ++ tailWord_1581118).sum := by decide
  have hdescent : baseEnd_1581118 < baseStart_1581118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581177 : List Nat := [1, 2, 1, 3, 4, 3, 1, 6]
def baseStart_1581177 : Nat := 118140960795 + 1581177 * 2 ^ 59
def prefixEnd_1581177 : Nat := 4983230072969 + 3 ^ 40 * 1581177 * 2
def baseEnd_1581177 : Nat := 120282044568039314283823

theorem tailTrace_1581177 : CollatzResearch.WordTrace tailWord_1581177 prefixEnd_1581177 120282044568039314283823 := by
  unfold tailWord_1581177
  simp only [CollatzResearch.WordTrace]
  refine ⟨57670262992673247377445785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38446841995115498251630523 57670262992673247377445785)
  ·
    refine ⟨43252697244504935533084339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57670262992673247377445785 43252697244504935533084339)
    ·
      refine ⟨64879045866757403299626509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43252697244504935533084339 64879045866757403299626509)
      ·
        refine ⟨24329642200034026237359941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64879045866757403299626509 24329642200034026237359941)
        ·
          refine ⟨4561807912506379919504989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24329642200034026237359941 4561807912506379919504989)
          ·
            refine ⟨1710677967189892469814371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4561807912506379919504989 1710677967189892469814371)
            ·
              refine ⟨2566016950784838704721557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710677967189892469814371 2566016950784838704721557)
              ·
                refine ⟨120282044568039314283823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2566016950784838704721557 120282044568039314283823)
                ·
                  rfl

theorem cell21_1581177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 6].length) (baseStart_1581177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581177 prefixEnd_1581177 := by exact prefixLift 1581177
  have htrace : WordTrace (prefixWord ++ tailWord_1581177) baseStart_1581177 baseEnd_1581177 := by
    simpa [prefixWord, tailWord_1581177, baseEnd_1581177] using wordTrace_append hprefix tailTrace_1581177
  have hstable : (prefixWord ++ tailWord_1581177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581177).length < 2 ^ (prefixWord ++ tailWord_1581177).sum := by decide
  have hdescent : baseEnd_1581177 < baseStart_1581177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581205 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_1581205 : Nat := 118140960795 + 1581205 * 2 ^ 59
def prefixEnd_1581205 : Nat := 4983230072969 + 3 ^ 40 * 1581205 * 2
def baseEnd_1581205 : Nat := 360852523685596116384745

theorem tailTrace_1581205 : CollatzResearch.WordTrace tailWord_1581205 prefixEnd_1581205 360852523685596116384745 := by
  unfold tailWord_1581205
  simp only [CollatzResearch.WordTrace]
  refine ⟨57671284236571808159465069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38447522824381205439643379 57671284236571808159465069)
  ·
    refine ⟨21626731588714428059799401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57671284236571808159465069 21626731588714428059799401)
    ·
      refine ⟨16220048691535821044849551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21626731588714428059799401 16220048691535821044849551)
      ·
        refine ⟨24330073037303731567274327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220048691535821044849551 24330073037303731567274327)
        ·
          refine ⟨36495109555955597350911491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330073037303731567274327 36495109555955597350911491)
          ·
            refine ⟨54742664333933396026367237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36495109555955597350911491 54742664333933396026367237)
            ·
              refine ⟨10264249562612511754943857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54742664333933396026367237 10264249562612511754943857)
              ·
                refine ⟨7698187171959383816207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10264249562612511754943857 7698187171959383816207893)
                ·
                  refine ⟨360852523685596116384745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7698187171959383816207893 360852523685596116384745)
                  ·
                    rfl

theorem cell21_1581205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_1581205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581205 prefixEnd_1581205 := by exact prefixLift 1581205
  have htrace : WordTrace (prefixWord ++ tailWord_1581205) baseStart_1581205 baseEnd_1581205 := by
    simpa [prefixWord, tailWord_1581205, baseEnd_1581205] using wordTrace_append hprefix tailTrace_1581205
  have hstable : (prefixWord ++ tailWord_1581205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581205).length < 2 ^ (prefixWord ++ tailWord_1581205).sum := by decide
  have hdescent : baseEnd_1581205 < baseStart_1581205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581239 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 4]
def baseStart_1581239 : Nat := 118140960795 + 1581239 * 2 ^ 59
def prefixEnd_1581239 : Nat := 4983230072969 + 3 ^ 40 * 1581239 * 2
def baseEnd_1581239 : Nat := 360860282948819612818009

theorem tailTrace_1581239 : CollatzResearch.WordTrace tailWord_1581239 prefixEnd_1581239 360860282948819612818009 := by
  unfold tailWord_1581239
  simp only [CollatzResearch.WordTrace]
  refine ⟨57672524318448631966202771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38448349545632421310801847 57672524318448631966202771)
  ·
    refine ⟨86508786477672947949304157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57672524318448631966202771 86508786477672947949304157)
    ·
      refine ⟨32440794929127355480989059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86508786477672947949304157 32440794929127355480989059)
      ·
        refine ⟨48661192393691033221483589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32440794929127355480989059 48661192393691033221483589)
        ·
          refine ⟨9123973573817068729028173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48661192393691033221483589 9123973573817068729028173)
          ·
            refine ⟨3421490090181400773385565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9123973573817068729028173 3421490090181400773385565)
            ·
              refine ⟨1283058783818025290019587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3421490090181400773385565 1283058783818025290019587)
              ·
                refine ⟨1924588175727037935029381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283058783818025290019587 1924588175727037935029381)
                ·
                  refine ⟨360860282948819612818009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1924588175727037935029381 360860282948819612818009)
                  ·
                    rfl

theorem cell21_1581239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 4].length) (baseStart_1581239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581239 prefixEnd_1581239 := by exact prefixLift 1581239
  have htrace : WordTrace (prefixWord ++ tailWord_1581239) baseStart_1581239 baseEnd_1581239 := by
    simpa [prefixWord, tailWord_1581239, baseEnd_1581239] using wordTrace_append hprefix tailTrace_1581239
  have hstable : (prefixWord ++ tailWord_1581239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581239).length < 2 ^ (prefixWord ++ tailWord_1581239).sum := by decide
  have hdescent : baseEnd_1581239 < baseStart_1581239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581270 : List Nat := [5, 2, 1, 2, 1, 3, 7]
def baseStart_1581270 : Nat := 118140960795 + 1581270 * 2 ^ 59
def prefixEnd_1581270 : Nat := 4983230072969 + 3 ^ 40 * 1581270 * 2
def baseEnd_1581270 : Nat := 40096373063463383089031

theorem tailTrace_1581270 : CollatzResearch.WordTrace tailWord_1581270 prefixEnd_1581270 40096373063463383089031 := by
  unfold tailWord_1581270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604603436333520266286329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38449103320890882840387509 3604603436333520266286329)
  ·
    refine ⟨2703452577250140199714747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3604603436333520266286329 2703452577250140199714747)
    ·
      refine ⟨4055178865875210299572121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703452577250140199714747 4055178865875210299572121)
      ·
        refine ⟨3041384149406407724679091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4055178865875210299572121 3041384149406407724679091)
        ·
          refine ⟨4562076224109611587018637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041384149406407724679091 4562076224109611587018637)
          ·
            refine ⟨1710778584041104345131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4562076224109611587018637 1710778584041104345131989)
            ·
              refine ⟨40096373063463383089031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1710778584041104345131989 40096373063463383089031)
              ·
                rfl

theorem cell21_1581270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 7].length) (baseStart_1581270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581270 prefixEnd_1581270 := by exact prefixLift 1581270
  have htrace : WordTrace (prefixWord ++ tailWord_1581270) baseStart_1581270 baseEnd_1581270 := by
    simpa [prefixWord, tailWord_1581270, baseEnd_1581270] using wordTrace_append hprefix tailTrace_1581270
  have hstable : (prefixWord ++ tailWord_1581270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581270).length < 2 ^ (prefixWord ++ tailWord_1581270).sum := by decide
  have hdescent : baseEnd_1581270 < baseStart_1581270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581281 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_1581281 : Nat := 118140960795 + 1581281 * 2 ^ 59
def prefixEnd_1581281 : Nat := 4983230072969 + 3 ^ 40 * 1581281 * 2
def baseEnd_1581281 : Nat := 360869867921036873117923

theorem tailTrace_1581281 : CollatzResearch.WordTrace tailWord_1581281 prefixEnd_1581281 360869867921036873117923 := by
  unfold tailWord_1581281
  simp only [CollatzResearch.WordTrace]
  refine ⟨57674056184296473139231697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38449370789530982092821131 57674056184296473139231697)
  ·
    refine ⟨43255542138222354854423773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57674056184296473139231697 43255542138222354854423773)
    ·
      refine ⟨16220828301833383070408915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43255542138222354854423773 16220828301833383070408915)
      ·
        refine ⟨24331242452750074605613373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220828301833383070408915 24331242452750074605613373)
        ·
          refine ⟨9124215919781277977105015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24331242452750074605613373 9124215919781277977105015)
          ·
            refine ⟨13686323879671916965657523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124215919781277977105015 13686323879671916965657523)
            ·
              refine ⟨20529485819507875448486285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13686323879671916965657523 20529485819507875448486285)
              ·
                refine ⟨7698557182315453293182357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20529485819507875448486285 7698557182315453293182357)
                ·
                  refine ⟨360869867921036873117923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7698557182315453293182357 360869867921036873117923)
                  ·
                    rfl

theorem cell21_1581281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_1581281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581281 prefixEnd_1581281 := by exact prefixLift 1581281
  have htrace : WordTrace (prefixWord ++ tailWord_1581281) baseStart_1581281 baseEnd_1581281 := by
    simpa [prefixWord, tailWord_1581281, baseEnd_1581281] using wordTrace_append hprefix tailTrace_1581281
  have hstable : (prefixWord ++ tailWord_1581281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581281).length < 2 ^ (prefixWord ++ tailWord_1581281).sum := by decide
  have hdescent : baseEnd_1581281 < baseStart_1581281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581464 : List Nat := [2, 1, 2, 5, 1, 1, 1, 8]
def baseStart_1581464 : Nat := 118140960795 + 1581464 * 2 ^ 59
def prefixEnd_1581464 : Nat := 4983230072969 + 3 ^ 40 * 1581464 * 2
def baseEnd_1581464 : Nat := 120303877004756407189183

theorem tailTrace_1581464 : CollatzResearch.WordTrace tailWord_1581464 prefixEnd_1581464 120303877004756407189183 := by
  unfold tailWord_1581464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28840365371316747696571723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38453820495088996928762297 28840365371316747696571723)
  ·
    refine ⟨43260548056975121544857585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28840365371316747696571723 43260548056975121544857585)
    ·
      refine ⟨32445411042731341158643189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43260548056975121544857585 32445411042731341158643189)
      ·
        refine ⟨3041757285256063233622799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32445411042731341158643189 3041757285256063233622799)
        ·
          refine ⟨4562635927884094850434199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041757285256063233622799 4562635927884094850434199)
          ·
            refine ⟨6843953891826142275651299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562635927884094850434199 6843953891826142275651299)
            ·
              refine ⟨10265930837739213413476949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6843953891826142275651299 10265930837739213413476949)
              ·
                refine ⟨120303877004756407189183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10265930837739213413476949 120303877004756407189183)
                ·
                  rfl

theorem cell21_1581464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_1581464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581464 prefixEnd_1581464 := by exact prefixLift 1581464
  have htrace : WordTrace (prefixWord ++ tailWord_1581464) baseStart_1581464 baseEnd_1581464 := by
    simpa [prefixWord, tailWord_1581464, baseEnd_1581464] using wordTrace_append hprefix tailTrace_1581464
  have hstable : (prefixWord ++ tailWord_1581464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581464).length < 2 ^ (prefixWord ++ tailWord_1581464).sum := by decide
  have hdescent : baseEnd_1581464 < baseStart_1581464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581512 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 3]
def baseStart_1581512 : Nat := 118140960795 + 1581512 * 2 ^ 59
def prefixEnd_1581512 : Nat := 4983230072969 + 3 ^ 40 * 1581512 * 2
def baseEnd_1581512 : Nat := 360922585268231804767451

theorem tailTrace_1581512 : CollatzResearch.WordTrace tailWord_1581512 prefixEnd_1581512 360922585268231804767451 := by
  unfold tailWord_1581512
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841240723229799795445395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38454987630973066393927193 28841240723229799795445395)
  ·
    refine ⟨43261861084844699693168093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28841240723229799795445395 43261861084844699693168093)
    ·
      refine ⟨16223197906816762384938035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43261861084844699693168093 16223197906816762384938035)
      ·
        refine ⟨24334796860225143577407053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16223197906816762384938035 24334796860225143577407053)
        ·
          refine ⟨9125548822584428841527645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24334796860225143577407053 9125548822584428841527645)
          ·
            refine ⟨3422080808469160815572867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9125548822584428841527645 3422080808469160815572867)
            ·
              refine ⟨5133121212703741223359301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422080808469160815572867 5133121212703741223359301)
              ·
                refine ⟨962460227381951479379869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5133121212703741223359301 962460227381951479379869)
                ·
                  refine ⟨360922585268231804767451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962460227381951479379869 360922585268231804767451)
                  ·
                    rfl

theorem cell21_1581512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 3].length) (baseStart_1581512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581512 prefixEnd_1581512 := by exact prefixLift 1581512
  have htrace : WordTrace (prefixWord ++ tailWord_1581512) baseStart_1581512 baseEnd_1581512 := by
    simpa [prefixWord, tailWord_1581512, baseEnd_1581512] using wordTrace_append hprefix tailTrace_1581512
  have hstable : (prefixWord ++ tailWord_1581512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581512).length < 2 ^ (prefixWord ++ tailWord_1581512).sum := by decide
  have hdescent : baseEnd_1581512 < baseStart_1581512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581557 : List Nat := [1, 3, 5, 1, 2, 1, 8]
def baseStart_1581557 : Nat := 118140960795 + 1581557 * 2 ^ 59
def prefixEnd_1581557 : Nat := 4983230072969 + 3 ^ 40 * 1581557 * 2
def baseEnd_1581557 : Nat := 40103650542369080724151

theorem tailTrace_1581557 : CollatzResearch.WordTrace tailWord_1581557 prefixEnd_1581557 40103650542369080724151 := by
  unfold tailWord_1581557
  simp only [CollatzResearch.WordTrace]
  refine ⟨57684122731296572276278925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456081820864381517519283 57684122731296572276278925)
  ·
    refine ⟨21631546024236214603604597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57684122731296572276278925 21631546024236214603604597)
    ·
      refine ⟨2027957439772145119087931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21631546024236214603604597 2027957439772145119087931)
      ·
        refine ⟨3041936159658217678631897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027957439772145119087931 3041936159658217678631897)
        ·
          refine ⟨2281452119743663258973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3041936159658217678631897 2281452119743663258973923)
          ·
            refine ⟨3422178179615494888460885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281452119743663258973923 3422178179615494888460885)
            ·
              refine ⟨40103650542369080724151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3422178179615494888460885 40103650542369080724151)
              ·
                rfl

theorem cell21_1581557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 8].length) (baseStart_1581557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581557 prefixEnd_1581557 := by exact prefixLift 1581557
  have htrace : WordTrace (prefixWord ++ tailWord_1581557) baseStart_1581557 baseEnd_1581557 := by
    simpa [prefixWord, tailWord_1581557, baseEnd_1581557] using wordTrace_append hprefix tailTrace_1581557
  have hstable : (prefixWord ++ tailWord_1581557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581557).length < 2 ^ (prefixWord ++ tailWord_1581557).sum := by decide
  have hdescent : baseEnd_1581557 < baseStart_1581557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581571 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 3]
def baseStart_1581571 : Nat := 118140960795 + 1581571 * 2 ^ 59
def prefixEnd_1581571 : Nat := 4983230072969 + 3 ^ 40 * 1581571 * 2
def baseEnd_1581571 : Nat := 360936049872060813283997

theorem tailTrace_1581571 : CollatzResearch.WordTrace tailWord_1581571 prefixEnd_1581571 360936049872060813283997 := by
  unfold tailWord_1581571
  simp only [CollatzResearch.WordTrace]
  refine ⟨57684633353245852667288567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456422235497235111525711 57684633353245852667288567)
  ·
    refine ⟨86526950029868779000932851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57684633353245852667288567 86526950029868779000932851)
    ·
      refine ⟨129790425044803168501399277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86526950029868779000932851 129790425044803168501399277)
      ·
        refine ⟨48671409391801188188024729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129790425044803168501399277 48671409391801188188024729)
        ·
          refine ⟨36503557043850891141018547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48671409391801188188024729 36503557043850891141018547)
          ·
            refine ⟨54755335565776336711527821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36503557043850891141018547 54755335565776336711527821)
            ·
              refine ⟨20533250837166126266822933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54755335565776336711527821 20533250837166126266822933)
              ·
                refine ⟨962496132992162168757325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20533250837166126266822933 962496132992162168757325)
                ·
                  refine ⟨360936049872060813283997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962496132992162168757325 360936049872060813283997)
                  ·
                    rfl

theorem cell21_1581571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].length) (baseStart_1581571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581571 prefixEnd_1581571 := by exact prefixLift 1581571
  have htrace : WordTrace (prefixWord ++ tailWord_1581571) baseStart_1581571 baseEnd_1581571 := by
    simpa [prefixWord, tailWord_1581571, baseEnd_1581571] using wordTrace_append hprefix tailTrace_1581571
  have hstable : (prefixWord ++ tailWord_1581571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581571).length < 2 ^ (prefixWord ++ tailWord_1581571).sum := by decide
  have hdescent : baseEnd_1581571 < baseStart_1581571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581588 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1581588 : Nat := 118140960795 + 1581588 * 2 ^ 59
def prefixEnd_1581588 : Nat := 4983230072969 + 3 ^ 40 * 1581588 * 2
def baseEnd_1581588 : Nat := 360939929503672561500629

theorem tailTrace_1581588 : CollatzResearch.WordTrace tailWord_1581588 prefixEnd_1581588 360939929503672561500629 := by
  unfold tailWord_1581588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842626697092132285328709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38456835596122843047104945 28842626697092132285328709)
  ·
    refine ⟨5407992505704774803499133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28842626697092132285328709 5407992505704774803499133)
    ·
      refine ⟨2027997189639290551312175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5407992505704774803499133 2027997189639290551312175)
      ·
        refine ⟨3041995784458935826968263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027997189639290551312175 3041995784458935826968263)
        ·
          refine ⟨4562993676688403740452395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041995784458935826968263 4562993676688403740452395)
          ·
            refine ⟨6844490515032605610678593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562993676688403740452395 6844490515032605610678593)
            ·
              refine ⟨5133367886274454208008945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844490515032605610678593 5133367886274454208008945)
              ·
                refine ⟨3850025914705840656006709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133367886274454208008945 3850025914705840656006709)
                ·
                  refine ⟨360939929503672561500629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850025914705840656006709 360939929503672561500629)
                  ·
                    rfl

theorem cell21_1581588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1581588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581588 prefixEnd_1581588 := by exact prefixLift 1581588
  have htrace : WordTrace (prefixWord ++ tailWord_1581588) baseStart_1581588 baseEnd_1581588 := by
    simpa [prefixWord, tailWord_1581588, baseEnd_1581588] using wordTrace_append hprefix tailTrace_1581588
  have hstable : (prefixWord ++ tailWord_1581588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581588).length < 2 ^ (prefixWord ++ tailWord_1581588).sum := by decide
  have hdescent : baseEnd_1581588 < baseStart_1581588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581591 : List Nat := [1, 1, 3, 6, 2, 1, 2, 5]
def baseStart_1581591 : Nat := 118140960795 + 1581591 * 2 ^ 59
def prefixEnd_1581591 : Nat := 4983230072969 + 3 ^ 40 * 1581591 * 2
def baseEnd_1581591 : Nat := 120313538048181740983541

theorem tailTrace_1581591 : CollatzResearch.WordTrace tailWord_1581591 prefixEnd_1581591 120313538048181740983541 := by
  unfold tailWord_1581591
  simp only [CollatzResearch.WordTrace]
  refine ⟨57685362813173396083016627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38456908542115597388677751 57685362813173396083016627)
  ·
    refine ⟨86528044219760094124524941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57685362813173396083016627 86528044219760094124524941)
    ·
      refine ⟨32448016582410035296696853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86528044219760094124524941 32448016582410035296696853)
      ·
        refine ⟨1521000777300470404532665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32448016582410035296696853 1521000777300470404532665)
        ·
          refine ⟨1140750582975352803399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521000777300470404532665 1140750582975352803399499)
          ·
            refine ⟨1711125874463029205099249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140750582975352803399499 1711125874463029205099249)
            ·
              refine ⟨1283344405847271903824437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711125874463029205099249 1283344405847271903824437)
              ·
                refine ⟨120313538048181740983541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283344405847271903824437 120313538048181740983541)
                ·
                  rfl

theorem cell21_1581591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 5].length) (baseStart_1581591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581591 prefixEnd_1581591 := by exact prefixLift 1581591
  have htrace : WordTrace (prefixWord ++ tailWord_1581591) baseStart_1581591 baseEnd_1581591 := by
    simpa [prefixWord, tailWord_1581591, baseEnd_1581591] using wordTrace_append hprefix tailTrace_1581591
  have hstable : (prefixWord ++ tailWord_1581591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581591).length < 2 ^ (prefixWord ++ tailWord_1581591).sum := by decide
  have hdescent : baseEnd_1581591 < baseStart_1581591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581622 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1581622 : Nat := 118140960795 + 1581622 * 2 ^ 59
def prefixEnd_1581622 : Nat := 4983230072969 + 3 ^ 40 * 1581622 * 2
def baseEnd_1581622 : Nat := 360947688766896057933893

theorem tailTrace_1581622 : CollatzResearch.WordTrace tailWord_1581622 prefixEnd_1581622 360947688766896057933893 := by
  unfold tailWord_1581622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605405842253818023587195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38457662317374058918263413 3605405842253818023587195)
  ·
    refine ⟨5408108763380727035380793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605405842253818023587195 5408108763380727035380793)
    ·
      refine ⟨4056081572535545276535595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5408108763380727035380793 4056081572535545276535595)
      ·
        refine ⟨6084122358803317914803393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056081572535545276535595 6084122358803317914803393)
        ·
          refine ⟨4563091769102488436102545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6084122358803317914803393 4563091769102488436102545)
          ·
            refine ⟨3422318826826866327076909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4563091769102488436102545 3422318826826866327076909)
            ·
              refine ⟨1283369560060074872653841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3422318826826866327076909 1283369560060074872653841)
              ·
                refine ⟨962527170045056154490381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283369560060074872653841 962527170045056154490381)
                ·
                  refine ⟨360947688766896057933893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962527170045056154490381 360947688766896057933893)
                  ·
                    rfl

theorem cell21_1581622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1581622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581622 prefixEnd_1581622 := by exact prefixLift 1581622
  have htrace : WordTrace (prefixWord ++ tailWord_1581622) baseStart_1581622 baseEnd_1581622 := by
    simpa [prefixWord, tailWord_1581622, baseEnd_1581622] using wordTrace_append hprefix tailTrace_1581622
  have hstable : (prefixWord ++ tailWord_1581622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581622).length < 2 ^ (prefixWord ++ tailWord_1581622).sum := by decide
  have hdescent : baseEnd_1581622 < baseStart_1581622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581678 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_1581678 : Nat := 118140960795 + 1581678 * 2 ^ 59
def prefixEnd_1581678 : Nat := 4983230072969 + 3 ^ 40 * 1581678 * 2
def baseEnd_1581678 : Nat := 360960468729852405000445

theorem tailTrace_1581678 : CollatzResearch.WordTrace tailWord_1581678 prefixEnd_1581678 360960468729852405000445 := by
  unfold tailWord_1581678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211066995482276242679211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38459023975905473294289125 7211066995482276242679211)
  ·
    refine ⟨10816600493223414364018817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7211066995482276242679211 10816600493223414364018817)
    ·
      refine ⟨8112450369917560773014113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10816600493223414364018817 8112450369917560773014113)
      ·
        refine ⟨6084337777438170579760585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8112450369917560773014113 6084337777438170579760585)
        ·
          refine ⟨4563253333078627934820439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6084337777438170579760585 4563253333078627934820439)
          ·
            refine ⟨6844879999617941902230659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563253333078627934820439 6844879999617941902230659)
            ·
              refine ⟨10267319999426912853345989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844879999617941902230659 10267319999426912853345989)
              ·
                refine ⟨1925122499892546160002373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10267319999426912853345989 1925122499892546160002373)
                ·
                  refine ⟨360960468729852405000445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925122499892546160002373 360960468729852405000445)
                  ·
                    rfl

theorem cell21_1581678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_1581678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581678 prefixEnd_1581678 := by exact prefixLift 1581678
  have htrace : WordTrace (prefixWord ++ tailWord_1581678) baseStart_1581678 baseEnd_1581678 := by
    simpa [prefixWord, tailWord_1581678, baseEnd_1581678] using wordTrace_append hprefix tailTrace_1581678
  have hstable : (prefixWord ++ tailWord_1581678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581678).length < 2 ^ (prefixWord ++ tailWord_1581678).sum := by decide
  have hdescent : baseEnd_1581678 < baseStart_1581678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581698 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 5]
def baseStart_1581698 : Nat := 118140960795 + 1581698 * 2 ^ 59
def prefixEnd_1581698 : Nat := 4983230072969 + 3 ^ 40 * 1581698 * 2
def baseEnd_1581698 : Nat := 360965033002336814667071

theorem tailTrace_1581698 : CollatzResearch.WordTrace tailWord_1581698 prefixEnd_1581698 360965033002336814667071 := by
  unfold tailWord_1581698
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422316355946438339290437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38459510282523835571441165 14422316355946438339290437)
  ·
    refine ⟨2704184316739957188616957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14422316355946438339290437 2704184316739957188616957)
    ·
      refine ⟨1014069118777483945731359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2704184316739957188616957 1014069118777483945731359)
      ·
        refine ⟨1521103678166225918597039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014069118777483945731359 1521103678166225918597039)
        ·
          refine ⟨2281655517249338877895559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521103678166225918597039 2281655517249338877895559)
          ·
            refine ⟨3422483275874008316843339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281655517249338877895559 3422483275874008316843339)
            ·
              refine ⟨5133724913811012475265009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422483275874008316843339 5133724913811012475265009)
              ·
                refine ⟨3850293685358259356448757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133724913811012475265009 3850293685358259356448757)
                ·
                  refine ⟨360965033002336814667071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850293685358259356448757 360965033002336814667071)
                  ·
                    rfl

theorem cell21_1581698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_1581698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581698 prefixEnd_1581698 := by exact prefixLift 1581698
  have htrace : WordTrace (prefixWord ++ tailWord_1581698) baseStart_1581698 baseEnd_1581698 := by
    simpa [prefixWord, tailWord_1581698, baseEnd_1581698] using wordTrace_append hprefix tailTrace_1581698
  have hstable : (prefixWord ++ tailWord_1581698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581698).length < 2 ^ (prefixWord ++ tailWord_1581698).sum := by decide
  have hdescent : baseEnd_1581698 < baseStart_1581698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581754 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_1581754 : Nat := 118140960795 + 1581754 * 2 ^ 59
def prefixEnd_1581754 : Nat := 4983230072969 + 3 ^ 40 * 1581754 * 2
def baseEnd_1581754 : Nat := 360977812965293161733623

theorem tailTrace_1581754 : CollatzResearch.WordTrace tailWord_1581754 prefixEnd_1581754 360977812965293161733623 := by
  unfold tailWord_1581754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422826977895718730300079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38460871941055249947466877 14422826977895718730300079)
  ·
    refine ⟨21634240466843578095450119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14422826977895718730300079 21634240466843578095450119)
    ·
      refine ⟨32451360700265367143175179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21634240466843578095450119 32451360700265367143175179)
      ·
        refine ⟨48677041050398050714762769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32451360700265367143175179 48677041050398050714762769)
        ·
          refine ⟨36507780787798538036072077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48677041050398050714762769 36507780787798538036072077)
          ·
            refine ⟨13690417795424451763527029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36507780787798538036072077 13690417795424451763527029)
            ·
              refine ⟨1283476668321042352830659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13690417795424451763527029 1283476668321042352830659)
              ·
                refine ⟨1925215002481563529245989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283476668321042352830659 1925215002481563529245989)
                ·
                  refine ⟨360977812965293161733623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925215002481563529245989 360977812965293161733623)
                  ·
                    rfl

theorem cell21_1581754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_1581754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581754 prefixEnd_1581754 := by exact prefixLift 1581754
  have htrace : WordTrace (prefixWord ++ tailWord_1581754) baseStart_1581754 baseEnd_1581754 := by
    simpa [prefixWord, tailWord_1581754, baseEnd_1581754] using wordTrace_append hprefix tailTrace_1581754
  have hstable : (prefixWord ++ tailWord_1581754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581754).length < 2 ^ (prefixWord ++ tailWord_1581754).sum := by decide
  have hdescent : baseEnd_1581754 < baseStart_1581754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581768 : List Nat := [2, 1, 3, 1, 2, 3, 4, 5]
def baseStart_1581768 : Nat := 118140960795 + 1581768 * 2 ^ 59
def prefixEnd_1581768 : Nat := 4983230072969 + 3 ^ 40 * 1581768 * 2
def baseEnd_1581768 : Nat := 120327002652010749500087

theorem tailTrace_1581768 : CollatzResearch.WordTrace tailWord_1581768 prefixEnd_1581768 120327002652010749500087 := by
  unfold tailWord_1581768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28845909266766077656104979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38461212355688103541473305 28845909266766077656104979)
  ·
    refine ⟨43268863900149116484157469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28845909266766077656104979 43268863900149116484157469)
    ·
      refine ⟨16225823962555918681559051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43268863900149116484157469 16225823962555918681559051)
      ·
        refine ⟨24338735943833878022338577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16225823962555918681559051 24338735943833878022338577)
        ·
          refine ⟨18254051957875408516753933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24338735943833878022338577 18254051957875408516753933)
          ·
            refine ⟨6845269484203278193782725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18254051957875408516753933 6845269484203278193782725)
            ·
              refine ⟨1283488028288114661334261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6845269484203278193782725 1283488028288114661334261)
              ·
                refine ⟨120327002652010749500087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283488028288114661334261 120327002652010749500087)
                ·
                  rfl

theorem cell21_1581768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_1581768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581768 prefixEnd_1581768 := by exact prefixLift 1581768
  have htrace : WordTrace (prefixWord ++ tailWord_1581768) baseStart_1581768 baseEnd_1581768 := by
    simpa [prefixWord, tailWord_1581768, baseEnd_1581768] using wordTrace_append hprefix tailTrace_1581768
  have hstable : (prefixWord ++ tailWord_1581768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581768).length < 2 ^ (prefixWord ++ tailWord_1581768).sum := by decide
  have hdescent : baseEnd_1581768 < baseStart_1581768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581844 : List Nat := [2, 4, 4, 11]
def baseStart_1581844 : Nat := 118140960795 + 1581844 * 2 ^ 59
def prefixEnd_1581844 : Nat := 4983230072969 + 3 ^ 40 * 1581844 * 2
def baseEnd_1581844 : Nat := 1485589926713880679973

theorem tailTrace_1581844 : CollatzResearch.WordTrace tailWord_1581844 prefixEnd_1581844 1485589926713880679973 := by
  unfold tailWord_1581844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28847295240628410145988293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38463060320837880194651057 28847295240628410145988293)
  ·
    refine ⟨5408867857617826902372805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28847295240628410145988293 5408867857617826902372805)
    ·
      refine ⟨1014162723303342544194901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5408867857617826902372805 1014162723303342544194901)
      ·
        refine ⟨1485589926713880679973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1014162723303342544194901 1485589926713880679973)
        ·
          rfl

theorem cell21_1581844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 11].length) (baseStart_1581844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581844 prefixEnd_1581844 := by exact prefixLift 1581844
  have htrace : WordTrace (prefixWord ++ tailWord_1581844) baseStart_1581844 baseEnd_1581844 := by
    simpa [prefixWord, tailWord_1581844, baseEnd_1581844] using wordTrace_append hprefix tailTrace_1581844
  have hstable : (prefixWord ++ tailWord_1581844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581844).length < 2 ^ (prefixWord ++ tailWord_1581844).sum := by decide
  have hdescent : baseEnd_1581844 < baseStart_1581844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581878 : List Nat := [5, 1, 2, 2, 2, 1, 3, 5]
def baseStart_1581878 : Nat := 118140960795 + 1581878 * 2 ^ 59
def prefixEnd_1581878 : Nat := 4983230072969 + 3 ^ 40 * 1581878 * 2
def baseEnd_1581878 : Nat := 120335370484898833888901

theorem tailTrace_1581878 : CollatzResearch.WordTrace tailWord_1581878 prefixEnd_1581878 120335370484898833888901 := by
  unfold tailWord_1581878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605989410195852756169643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38463887042089096065809525 3605989410195852756169643)
  ·
    refine ⟨5408984115293779134254465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605989410195852756169643 5408984115293779134254465)
    ·
      refine ⟨4056738086470334350690849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5408984115293779134254465 4056738086470334350690849)
      ·
        refine ⟨3042553564852750763018137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4056738086470334350690849 3042553564852750763018137)
        ·
          refine ⟨2281915173639563072263603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3042553564852750763018137 2281915173639563072263603)
          ·
            refine ⟨3422872760459344608395405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281915173639563072263603 3422872760459344608395405)
            ·
              refine ⟨1283577285172254228148277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3422872760459344608395405 1283577285172254228148277)
              ·
                refine ⟨120335370484898833888901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283577285172254228148277 120335370484898833888901)
                ·
                  rfl

theorem cell21_1581878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_1581878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581878 prefixEnd_1581878 := by exact prefixLift 1581878
  have htrace : WordTrace (prefixWord ++ tailWord_1581878) baseStart_1581878 baseEnd_1581878 := by
    simpa [prefixWord, tailWord_1581878, baseEnd_1581878] using wordTrace_append hprefix tailTrace_1581878
  have hstable : (prefixWord ++ tailWord_1581878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581878).length < 2 ^ (prefixWord ++ tailWord_1581878).sum := by decide
  have hdescent : baseEnd_1581878 < baseStart_1581878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581951 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 3]
def baseStart_1581951 : Nat := 118140960795 + 1581951 * 2 ^ 59
def prefixEnd_1581951 : Nat := 4983230072969 + 3 ^ 40 * 1581951 * 2
def baseEnd_1581951 : Nat := 361022771049264596949887

theorem tailTrace_1581951 : CollatzResearch.WordTrace tailWord_1581951 prefixEnd_1581951 361022771049264596949887 := by
  unfold tailWord_1581951
  simp only [CollatzResearch.WordTrace]
  refine ⟨57698493091869177566121707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38465662061246118377414471 57698493091869177566121707)
  ·
    refine ⟨86547739637803766349182561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57698493091869177566121707 86547739637803766349182561)
    ·
      refine ⟨64910804728352824761886921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86547739637803766349182561 64910804728352824761886921)
      ·
        refine ⟨48683103546264618571415191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64910804728352824761886921 48683103546264618571415191)
        ·
          refine ⟨73024655319396927857122787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48683103546264618571415191 73024655319396927857122787)
          ·
            refine ⟨109536982979095391785684181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73024655319396927857122787 109536982979095391785684181)
            ·
              refine ⟨2567273038572548244976973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 109536982979095391785684181 2567273038572548244976973)
              ·
                refine ⟨962727389464705591866365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567273038572548244976973 962727389464705591866365)
                ·
                  refine ⟨361022771049264596949887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962727389464705591866365 361022771049264596949887)
                  ·
                    rfl

theorem cell21_1581951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 3].length) (baseStart_1581951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581951 prefixEnd_1581951 := by exact prefixLift 1581951
  have htrace : WordTrace (prefixWord ++ tailWord_1581951) baseStart_1581951 baseEnd_1581951 := by
    simpa [prefixWord, tailWord_1581951, baseEnd_1581951] using wordTrace_append hprefix tailTrace_1581951
  have hstable : (prefixWord ++ tailWord_1581951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581951).length < 2 ^ (prefixWord ++ tailWord_1581951).sum := by decide
  have hdescent : baseEnd_1581951 < baseStart_1581951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581954 : List Nat := [3, 4, 2, 2, 1, 2, 7]
def baseStart_1581954 : Nat := 118140960795 + 1581954 * 2 ^ 59
def prefixEnd_1581954 : Nat := 4983230072969 + 3 ^ 40 * 1581954 * 2
def baseEnd_1581954 : Nat := 40113717298904139822209

theorem tailTrace_1581954 : CollatzResearch.WordTrace tailWord_1581954 prefixEnd_1581954 40113717298904139822209 := by
  unfold tailWord_1581954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14424650627714577269620229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38465735007238872718987277 14424650627714577269620229)
  ·
    refine ⟨2704621992696483238053793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14424650627714577269620229 2704621992696483238053793)
    ·
      refine ⟨2028466494522362428540345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2704621992696483238053793 2028466494522362428540345)
      ·
        refine ⟨1521349870891771821405259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2028466494522362428540345 1521349870891771821405259)
        ·
          refine ⟨2282024806337657732107889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521349870891771821405259 2282024806337657732107889)
          ·
            refine ⟨1711518604753243299080917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282024806337657732107889 1711518604753243299080917)
            ·
              refine ⟨40113717298904139822209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1711518604753243299080917 40113717298904139822209)
              ·
                rfl

theorem cell21_1581954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 7].length) (baseStart_1581954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581954 prefixEnd_1581954 := by exact prefixLift 1581954
  have htrace : WordTrace (prefixWord ++ tailWord_1581954) baseStart_1581954 baseEnd_1581954 := by
    simpa [prefixWord, tailWord_1581954, baseEnd_1581954] using wordTrace_append hprefix tailTrace_1581954
  have hstable : (prefixWord ++ tailWord_1581954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581954).length < 2 ^ (prefixWord ++ tailWord_1581954).sum := by decide
  have hdescent : baseEnd_1581954 < baseStart_1581954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1581993 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 7]
def baseStart_1581993 : Nat := 118140960795 + 1581993 * 2 ^ 59
def prefixEnd_1581993 : Nat := 4983230072969 + 3 ^ 40 * 1581993 * 2
def baseEnd_1581993 : Nat := 361032356021481857249801

theorem tailTrace_1581993 : CollatzResearch.WordTrace tailWord_1581993 prefixEnd_1581993 361032356021481857249801 := by
  unfold tailWord_1581993
  simp only [CollatzResearch.WordTrace]
  refine ⟨57700024957717018739150633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38466683305144679159433755 57700024957717018739150633)
  ·
    refine ⟨43275018718287764054362975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57700024957717018739150633 43275018718287764054362975)
    ·
      refine ⟨64912528077431646081544463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43275018718287764054362975 64912528077431646081544463)
      ·
        refine ⟨97368792116147469122316695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64912528077431646081544463 97368792116147469122316695)
        ·
          refine ⟨146053188174221203683475043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97368792116147469122316695 146053188174221203683475043)
          ·
            refine ⟨219079782261331805525212565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146053188174221203683475043 219079782261331805525212565)
            ·
              refine ⟨10269364793499928383994339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219079782261331805525212565 10269364793499928383994339)
              ·
                refine ⟨15404047190249892575991509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10269364793499928383994339 15404047190249892575991509)
                ·
                  refine ⟨361032356021481857249801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15404047190249892575991509 361032356021481857249801)
                  ·
                    rfl

theorem cell21_1581993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 7].length) (baseStart_1581993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1581993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1581993 prefixEnd_1581993 := by exact prefixLift 1581993
  have htrace : WordTrace (prefixWord ++ tailWord_1581993) baseStart_1581993 baseEnd_1581993 := by
    simpa [prefixWord, tailWord_1581993, baseEnd_1581993] using wordTrace_append hprefix tailTrace_1581993
  have hstable : (prefixWord ++ tailWord_1581993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1581993).length < 2 ^ (prefixWord ++ tailWord_1581993).sum := by decide
  have hdescent : baseEnd_1581993 < baseStart_1581993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1581993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582027 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 3]
def baseStart_1582027 : Nat := 118140960795 + 1582027 * 2 ^ 59
def prefixEnd_1582027 : Nat := 4983230072969 + 3 ^ 40 * 1582027 * 2
def baseEnd_1582027 : Nat := 361040115284705353683065

theorem tailTrace_1582027 : CollatzResearch.WordTrace tailWord_1582027 prefixEnd_1582027 361040115284705353683065 := by
  unfold tailWord_1582027
  simp only [CollatzResearch.WordTrace]
  refine ⟨57701265039593842545888335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38467510026395895030592223 57701265039593842545888335)
  ·
    refine ⟨86551897559390763818832503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57701265039593842545888335 86551897559390763818832503)
    ·
      refine ⟨129827846339086145728248755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86551897559390763818832503 129827846339086145728248755)
      ·
        refine ⟨194741769508629218592373133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129827846339086145728248755 194741769508629218592373133)
        ·
          refine ⟨73028163565735956972139925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194741769508629218592373133 73028163565735956972139925)
          ·
            refine ⟨3423195167143872983069059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73028163565735956972139925 3423195167143872983069059)
            ·
              refine ⟨5134792750715809474603589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423195167143872983069059 5134792750715809474603589)
              ·
                refine ⟨962773640759214276488173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5134792750715809474603589 962773640759214276488173)
                ·
                  refine ⟨361040115284705353683065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962773640759214276488173 361040115284705353683065)
                  ·
                    rfl

theorem cell21_1582027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].length) (baseStart_1582027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582027 prefixEnd_1582027 := by exact prefixLift 1582027
  have htrace : WordTrace (prefixWord ++ tailWord_1582027) baseStart_1582027 baseEnd_1582027 := by
    simpa [prefixWord, tailWord_1582027, baseEnd_1582027] using wordTrace_append hprefix tailTrace_1582027
  have hstable : (prefixWord ++ tailWord_1582027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582027).length < 2 ^ (prefixWord ++ tailWord_1582027).sum := by decide
  have hdescent : baseEnd_1582027 < baseStart_1582027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582041 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 4]
def baseStart_1582041 : Nat := 118140960795 + 1582041 * 2 ^ 59
def prefixEnd_1582041 : Nat := 4983230072969 + 3 ^ 40 * 1582041 * 2
def baseEnd_1582041 : Nat := 361043310275444440449703

theorem tailTrace_1582041 : CollatzResearch.WordTrace tailWord_1582041 prefixEnd_1582041 361043310275444440449703 := by
  unfold tailWord_1582041
  simp only [CollatzResearch.WordTrace]
  refine ⟨57701775661543122936897977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38467850441028748624598651 57701775661543122936897977)
  ·
    refine ⟨43276331746157342202673483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57701775661543122936897977 43276331746157342202673483)
    ·
      refine ⟨64914497619236013304010225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43276331746157342202673483 64914497619236013304010225)
      ·
        refine ⟨48685873214427009978007669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64914497619236013304010225 48685873214427009978007669)
        ·
          refine ⟨4564300613852532185438219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48685873214427009978007669 4564300613852532185438219)
          ·
            refine ⟨6846450920778798278157329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564300613852532185438219 6846450920778798278157329)
            ·
              refine ⟨5134838190584098708617997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846450920778798278157329 5134838190584098708617997)
              ·
                refine ⟨1925564321469037015731749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5134838190584098708617997 1925564321469037015731749)
                ·
                  refine ⟨361043310275444440449703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925564321469037015731749 361043310275444440449703)
                  ·
                    rfl

theorem cell21_1582041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 4].length) (baseStart_1582041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582041 prefixEnd_1582041 := by exact prefixLift 1582041
  have htrace : WordTrace (prefixWord ++ tailWord_1582041) baseStart_1582041 baseEnd_1582041 := by
    simpa [prefixWord, tailWord_1582041, baseEnd_1582041] using wordTrace_append hprefix tailTrace_1582041
  have hstable : (prefixWord ++ tailWord_1582041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582041).length < 2 ^ (prefixWord ++ tailWord_1582041).sum := by decide
  have hdescent : baseEnd_1582041 < baseStart_1582041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582252 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_1582252 : Nat := 118140960795 + 1582252 * 2 ^ 59
def prefixEnd_1582252 : Nat := 4983230072969 + 3 ^ 40 * 1582252 * 2
def baseEnd_1582252 : Nat := 361091463350154962432605

theorem tailTrace_1582252 : CollatzResearch.WordTrace tailWord_1582252 prefixEnd_1582252 361091463350154962432605 := by
  unfold tailWord_1582252
  simp only [CollatzResearch.WordTrace]
  refine ⟨28854735731889352986414505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38472980975852470648552673 28854735731889352986414505)
  ·
    refine ⟨21641051798917014739810879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28854735731889352986414505 21641051798917014739810879)
    ·
      refine ⟨32461577698375522109716319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641051798917014739810879 32461577698375522109716319)
      ·
        refine ⟨48692366547563283164574479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32461577698375522109716319 48692366547563283164574479)
        ·
          refine ⟨73038549821344924746861719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48692366547563283164574479 73038549821344924746861719)
          ·
            refine ⟨109557824732017387120292579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73038549821344924746861719 109557824732017387120292579)
            ·
              refine ⟨164336737098026080680438869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109557824732017387120292579 164336737098026080680438869)
              ·
                refine ⟨1925821137867493132973893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 164336737098026080680438869 1925821137867493132973893)
                ·
                  refine ⟨361091463350154962432605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925821137867493132973893 361091463350154962432605)
                  ·
                    rfl

theorem cell21_1582252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_1582252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582252 prefixEnd_1582252 := by exact prefixLift 1582252
  have htrace : WordTrace (prefixWord ++ tailWord_1582252) baseStart_1582252 baseEnd_1582252 := by
    simpa [prefixWord, tailWord_1582252, baseEnd_1582252] using wordTrace_append hprefix tailTrace_1582252
  have hstable : (prefixWord ++ tailWord_1582252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582252).length < 2 ^ (prefixWord ++ tailWord_1582252).sum := by decide
  have hdescent : baseEnd_1582252 < baseStart_1582252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582266 : List Nat := [3, 1, 1, 1, 2, 2, 1, 10]
def baseStart_1582266 : Nat := 118140960795 + 1582266 * 2 ^ 59
def prefixEnd_1582266 : Nat := 4983230072969 + 3 ^ 40 * 1582266 * 2
def baseEnd_1582266 : Nat := 120364886113631349733081

theorem tailTrace_1582266 : CollatzResearch.WordTrace tailWord_1582266 prefixEnd_1582266 120364886113631349733081 := by
  unfold tailWord_1582266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427495521431996590959663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38473321390485324242559101 14427495521431996590959663)
  ·
    refine ⟨21641243282147994886439495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14427495521431996590959663 21641243282147994886439495)
    ·
      refine ⟨32461864923221992329659243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641243282147994886439495 32461864923221992329659243)
      ·
        refine ⟨48692797384832988494488865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32461864923221992329659243 48692797384832988494488865)
        ·
          refine ⟨36519598038624741370866649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48692797384832988494488865 36519598038624741370866649)
          ·
            refine ⟨27389698528968556028149987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36519598038624741370866649 27389698528968556028149987)
            ·
              refine ⟨41084547793452834042224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27389698528968556028149987 41084547793452834042224981)
              ·
                refine ⟨120364886113631349733081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41084547793452834042224981 120364886113631349733081)
                ·
                  rfl

theorem cell21_1582266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_1582266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582266 prefixEnd_1582266 := by exact prefixLift 1582266
  have htrace : WordTrace (prefixWord ++ tailWord_1582266) baseStart_1582266 baseEnd_1582266 := by
    simpa [prefixWord, tailWord_1582266, baseEnd_1582266] using wordTrace_append hprefix tailTrace_1582266
  have hstable : (prefixWord ++ tailWord_1582266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582266).length < 2 ^ (prefixWord ++ tailWord_1582266).sum := by decide
  have hdescent : baseEnd_1582266 < baseStart_1582266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582314 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1582314 : Nat := 118140960795 + 1582314 * 2 ^ 59
def prefixEnd_1582314 : Nat := 4983230072969 + 3 ^ 40 * 1582314 * 2
def baseEnd_1582314 : Nat := 361105612594856632399145

theorem tailTrace_1582314 : CollatzResearch.WordTrace tailWord_1582314 prefixEnd_1582314 361105612594856632399145 := by
  unfold tailWord_1582314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427933197388522640396499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38474488526369393707723997 14427933197388522640396499)
  ·
    refine ⟨21641899796082783960594749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14427933197388522640396499 21641899796082783960594749)
    ·
      refine ⟨8115712423531043985223031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21641899796082783960594749 8115712423531043985223031)
      ·
        refine ⟨12173568635296565977834547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115712423531043985223031 12173568635296565977834547)
        ·
          refine ⟨18260352952944848966751821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173568635296565977834547 18260352952944848966751821)
          ·
            refine ⟨6847632357354318362531933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18260352952944848966751821 6847632357354318362531933)
            ·
              refine ⟨2567862134007869385949475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847632357354318362531933 2567862134007869385949475)
              ·
                refine ⟨3851793201011804078924213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567862134007869385949475 3851793201011804078924213)
                ·
                  refine ⟨361105612594856632399145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851793201011804078924213 361105612594856632399145)
                  ·
                    rfl

theorem cell21_1582314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1582314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582314 prefixEnd_1582314 := by exact prefixLift 1582314
  have htrace : WordTrace (prefixWord ++ tailWord_1582314) baseStart_1582314 baseEnd_1582314 := by
    simpa [prefixWord, tailWord_1582314, baseEnd_1582314] using wordTrace_append hprefix tailTrace_1582314
  have hstable : (prefixWord ++ tailWord_1582314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582314).length < 2 ^ (prefixWord ++ tailWord_1582314).sum := by decide
  have hdescent : baseEnd_1582314 < baseStart_1582314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582365 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 3]
def baseStart_1582365 : Nat := 118140960795 + 1582365 * 2 ^ 59
def prefixEnd_1582365 : Nat := 4983230072969 + 3 ^ 40 * 1582365 * 2
def baseEnd_1582365 : Nat := 361117251489691877049041

theorem tailTrace_1582365 : CollatzResearch.WordTrace tailWord_1582365 prefixEnd_1582365 361117251489691877049041 := by
  unfold tailWord_1582365
  simp only [CollatzResearch.WordTrace]
  refine ⟨57713592912369326271692549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38475728608246217514461699 57713592912369326271692549)
  ·
    refine ⟨10821298671069248675942353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57713592912369326271692549 10821298671069248675942353)
    ·
      refine ⟨8115974003301936506956765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10821298671069248675942353 8115974003301936506956765)
      ·
        refine ⟨3043490251238226190108787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8115974003301936506956765 3043490251238226190108787)
        ·
          refine ⟨4565235376857339285163181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043490251238226190108787 4565235376857339285163181)
          ·
            refine ⟨1711963266321502231936193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4565235376857339285163181 1711963266321502231936193)
            ·
              refine ⟨1283972449741126673952145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711963266321502231936193 1283972449741126673952145)
              ·
                refine ⟨962979337305845005464109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283972449741126673952145 962979337305845005464109)
                ·
                  refine ⟨361117251489691877049041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962979337305845005464109 361117251489691877049041)
                  ·
                    rfl

theorem cell21_1582365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_1582365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582365 prefixEnd_1582365 := by exact prefixLift 1582365
  have htrace : WordTrace (prefixWord ++ tailWord_1582365) baseStart_1582365 baseEnd_1582365 := by
    simpa [prefixWord, tailWord_1582365, baseEnd_1582365] using wordTrace_append hprefix tailTrace_1582365
  have hstable : (prefixWord ++ tailWord_1582365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582365).length < 2 ^ (prefixWord ++ tailWord_1582365).sum := by decide
  have hdescent : baseEnd_1582365 < baseStart_1582365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582376 : List Nat := [2, 1, 5, 1, 2, 3, 1, 6]
def baseStart_1582376 : Nat := 118140960795 + 1582376 * 2 ^ 59
def prefixEnd_1582376 : Nat := 4983230072969 + 3 ^ 40 * 1582376 * 2
def baseEnd_1582376 : Nat := 120373253946519434121895

theorem tailTrace_1582376 : CollatzResearch.WordTrace tailWord_1582376 prefixEnd_1582376 120373253946519434121895 := by
  unfold tailWord_1582376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28856997057664737575171491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38475996076886316766895321 28856997057664737575171491)
  ·
    refine ⟨43285495586497106362757237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28856997057664737575171491 43285495586497106362757237)
    ·
      refine ⟨4058015211234103721508491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43285495586497106362757237 4058015211234103721508491)
      ·
        refine ⟨6087022816851155582262737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058015211234103721508491 6087022816851155582262737)
        ·
          refine ⟨4565267112638366686697053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087022816851155582262737 4565267112638366686697053)
          ·
            refine ⟨1711975167239387507511395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4565267112638366686697053 1711975167239387507511395)
            ·
              refine ⟨2567962750859081261267093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711975167239387507511395 2567962750859081261267093)
              ·
                refine ⟨120373253946519434121895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2567962750859081261267093 120373253946519434121895)
                ·
                  rfl

theorem cell21_1582376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_1582376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582376 prefixEnd_1582376 := by exact prefixLift 1582376
  have htrace : WordTrace (prefixWord ++ tailWord_1582376) baseStart_1582376 baseEnd_1582376 := by
    simpa [prefixWord, tailWord_1582376, baseEnd_1582376] using wordTrace_append hprefix tailTrace_1582376
  have hstable : (prefixWord ++ tailWord_1582376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582376).length < 2 ^ (prefixWord ++ tailWord_1582376).sum := by decide
  have hdescent : baseEnd_1582376 < baseStart_1582376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582407 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 3]
def baseStart_1582407 : Nat := 118140960795 + 1582407 * 2 ^ 59
def prefixEnd_1582407 : Nat := 4983230072969 + 3 ^ 40 * 1582407 * 2
def baseEnd_1582407 : Nat := 361126836461909137348955

theorem tailTrace_1582407 : CollatzResearch.WordTrace tailWord_1582407 prefixEnd_1582407 361126836461909137348955 := by
  unfold tailWord_1582407
  simp only [CollatzResearch.WordTrace]
  refine ⟨57715124778217167444721475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38476749852144778296480983 57715124778217167444721475)
  ·
    refine ⟨86572687167325751167082213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57715124778217167444721475 86572687167325751167082213)
    ·
      refine ⟨16232378843873578343827915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86572687167325751167082213 16232378843873578343827915)
      ·
        refine ⟨24348568265810367515741873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16232378843873578343827915 24348568265810367515741873)
        ·
          refine ⟨18261426199357775636806405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24348568265810367515741873 18261426199357775636806405)
          ·
            refine ⟨3424017412379582931901201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18261426199357775636806405 3424017412379582931901201)
            ·
              refine ⟨2568013059284687198925901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3424017412379582931901201 2568013059284687198925901)
              ·
                refine ⟨963004897231757699597213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568013059284687198925901 963004897231757699597213)
                ·
                  refine ⟨361126836461909137348955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963004897231757699597213 361126836461909137348955)
                  ·
                    rfl

theorem cell21_1582407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 3].length) (baseStart_1582407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582407 prefixEnd_1582407 := by exact prefixLift 1582407
  have htrace : WordTrace (prefixWord ++ tailWord_1582407) baseStart_1582407 baseEnd_1582407 := by
    simpa [prefixWord, tailWord_1582407, baseEnd_1582407] using wordTrace_append hprefix tailTrace_1582407
  have hstable : (prefixWord ++ tailWord_1582407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582407).length < 2 ^ (prefixWord ++ tailWord_1582407).sum := by decide
  have hdescent : baseEnd_1582407 < baseStart_1582407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582421 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 4]
def baseStart_1582421 : Nat := 118140960795 + 1582421 * 2 ^ 59
def prefixEnd_1582421 : Nat := 4983230072969 + 3 ^ 40 * 1582421 * 2
def baseEnd_1582421 : Nat := 361130031452648224115593

theorem tailTrace_1582421 : CollatzResearch.WordTrace tailWord_1582421 prefixEnd_1582421 361130031452648224115593 := by
  unfold tailWord_1582421
  simp only [CollatzResearch.WordTrace]
  refine ⟨57715635400166447835731117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38477090266777631890487411 57715635400166447835731117)
  ·
    refine ⟨21643363275062417938399169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57715635400166447835731117 21643363275062417938399169)
    ·
      refine ⟨16232522456296813453799377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21643363275062417938399169 16232522456296813453799377)
      ·
        refine ⟨12174391842222610090349533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16232522456296813453799377 12174391842222610090349533)
        ·
          refine ⟨4565396940833478783881075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12174391842222610090349533 4565396940833478783881075)
          ·
            refine ⟨6848095411250218175821613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565396940833478783881075 6848095411250218175821613)
            ·
              refine ⟨2568035779218831815933105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6848095411250218175821613 2568035779218831815933105)
              ·
                refine ⟨1926026834414123861949829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2568035779218831815933105 1926026834414123861949829)
                ·
                  refine ⟨361130031452648224115593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926026834414123861949829 361130031452648224115593)
                  ·
                    rfl

theorem cell21_1582421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_1582421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582421 prefixEnd_1582421 := by exact prefixLift 1582421
  have htrace : WordTrace (prefixWord ++ tailWord_1582421) baseStart_1582421 baseEnd_1582421 := by
    simpa [prefixWord, tailWord_1582421, baseEnd_1582421] using wordTrace_append hprefix tailTrace_1582421
  have hstable : (prefixWord ++ tailWord_1582421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582421).length < 2 ^ (prefixWord ++ tailWord_1582421).sum := by decide
  have hdescent : baseEnd_1582421 < baseStart_1582421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582449 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_1582449 : Nat := 118140960795 + 1582449 * 2 ^ 59
def prefixEnd_1582449 : Nat := 4983230072969 + 3 ^ 40 * 1582449 * 2
def baseEnd_1582449 : Nat := 361136421434126397648869

theorem tailTrace_1582449 : CollatzResearch.WordTrace tailWord_1582449 prefixEnd_1582449 361136421434126397648869 := by
  unfold tailWord_1582449
  simp only [CollatzResearch.WordTrace]
  refine ⟨57716656644065008617750401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38477771096043339078500267 57716656644065008617750401)
  ·
    refine ⟨43287492483048756463312801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57716656644065008617750401 43287492483048756463312801)
    ·
      refine ⟨32465619362286567347484601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43287492483048756463312801 32465619362286567347484601)
      ·
        refine ⟨24349214521714925510613451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465619362286567347484601 24349214521714925510613451)
        ·
          refine ⟨36523821782572388265920177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24349214521714925510613451 36523821782572388265920177)
          ·
            refine ⟨27392866336929291199440133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36523821782572388265920177 27392866336929291199440133)
            ·
              refine ⟨5136162438174242099895025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27392866336929291199440133 5136162438174242099895025)
              ·
                refine ⟨3852121828630681574921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5136162438174242099895025 3852121828630681574921269)
                ·
                  refine ⟨361136421434126397648869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3852121828630681574921269 361136421434126397648869)
                  ·
                    rfl

theorem cell21_1582449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_1582449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582449 prefixEnd_1582449 := by exact prefixLift 1582449
  have htrace : WordTrace (prefixWord ++ tailWord_1582449) baseStart_1582449 baseEnd_1582449 := by
    simpa [prefixWord, tailWord_1582449, baseEnd_1582449] using wordTrace_append hprefix tailTrace_1582449
  have hstable : (prefixWord ++ tailWord_1582449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582449).length < 2 ^ (prefixWord ++ tailWord_1582449).sum := by decide
  have hdescent : baseEnd_1582449 < baseStart_1582449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582539 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_1582539 : Nat := 118140960795 + 1582539 * 2 ^ 59
def prefixEnd_1582539 : Nat := 4983230072969 + 3 ^ 40 * 1582539 * 2
def baseEnd_1582539 : Nat := 361156960660306241148685

theorem tailTrace_1582539 : CollatzResearch.WordTrace tailWord_1582539 prefixEnd_1582539 361156960660306241148685 := by
  unfold tailWord_1582539
  simp only [CollatzResearch.WordTrace]
  refine ⟨57719939213738953988526671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38479959475825969325684447 57719939213738953988526671)
  ·
    refine ⟨86579908820608430982790007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57719939213738953988526671 86579908820608430982790007)
    ·
      refine ⟨129869863230912646474185011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86579908820608430982790007 129869863230912646474185011)
      ·
        refine ⟨194804794846368969711277517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129869863230912646474185011 194804794846368969711277517)
        ·
          refine ⟨73051798067388363641729069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194804794846368969711277517 73051798067388363641729069)
          ·
            refine ⟨27394424275270636365648401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73051798067388363641729069 27394424275270636365648401)
            ·
              refine ⟨20545818206452977274236301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27394424275270636365648401 20545818206452977274236301)
              ·
                refine ⟨7704681827419866477838613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545818206452977274236301 7704681827419866477838613)
                ·
                  refine ⟨361156960660306241148685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7704681827419866477838613 361156960660306241148685)
                  ·
                    rfl

theorem cell21_1582539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_1582539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582539 prefixEnd_1582539 := by exact prefixLift 1582539
  have htrace : WordTrace (prefixWord ++ tailWord_1582539) baseStart_1582539 baseEnd_1582539 := by
    simpa [prefixWord, tailWord_1582539, baseEnd_1582539] using wordTrace_append hprefix tailTrace_1582539
  have hstable : (prefixWord ++ tailWord_1582539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582539).length < 2 ^ (prefixWord ++ tailWord_1582539).sum := by decide
  have hdescent : baseEnd_1582539 < baseStart_1582539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582590 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1582590 : Nat := 118140960795 + 1582590 * 2 ^ 59
def prefixEnd_1582590 : Nat := 4983230072969 + 3 ^ 40 * 1582590 * 2
def baseEnd_1582590 : Nat := 361168599555141485798581

theorem tailTrace_1582590 : CollatzResearch.WordTrace tailWord_1582590 prefixEnd_1582590 361168599555141485798581 := by
  unfold tailWord_1582590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215224917069273712329153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38481199557702793132422149 7215224917069273712329153)
  ·
    refine ⟨5411418687801955284246865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7215224917069273712329153 5411418687801955284246865)
    ·
      refine ⟨4058564015851466463185149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5411418687801955284246865 4058564015851466463185149)
      ·
        refine ⟨1521961505944299923694431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4058564015851466463185149 1521961505944299923694431)
        ·
          refine ⟨2282942258916449885541647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521961505944299923694431 2282942258916449885541647)
          ·
            refine ⟨3424413388374674828312471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282942258916449885541647 3424413388374674828312471)
            ·
              refine ⟨5136620082562012242468707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424413388374674828312471 5136620082562012242468707)
              ·
                refine ⟨7704930123843018363703061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136620082562012242468707 7704930123843018363703061)
                ·
                  refine ⟨361168599555141485798581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7704930123843018363703061 361168599555141485798581)
                  ·
                    rfl

theorem cell21_1582590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1582590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582590 prefixEnd_1582590 := by exact prefixLift 1582590
  have htrace : WordTrace (prefixWord ++ tailWord_1582590) baseStart_1582590 baseEnd_1582590 := by
    simpa [prefixWord, tailWord_1582590, baseEnd_1582590] using wordTrace_append hprefix tailTrace_1582590
  have hstable : (prefixWord ++ tailWord_1582590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582590).length < 2 ^ (prefixWord ++ tailWord_1582590).sum := by decide
  have hdescent : baseEnd_1582590 < baseStart_1582590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1582601 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 5]
def baseStart_1582601 : Nat := 118140960795 + 1582601 * 2 ^ 59
def prefixEnd_1582601 : Nat := 4983230072969 + 3 ^ 40 * 1582601 * 2
def baseEnd_1582601 : Nat := 361171109905007911115225

theorem tailTrace_1582601 : CollatzResearch.WordTrace tailWord_1582601 prefixEnd_1582601 361171109905007911115225 := by
  unfold tailWord_1582601
  simp only [CollatzResearch.WordTrace]
  refine ⟨57722200539514338577283657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38481467026342892384855771 57722200539514338577283657)
  ·
    refine ⟨43291650404635753932962743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57722200539514338577283657 43291650404635753932962743)
    ·
      refine ⟨64937475606953630899444115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43291650404635753932962743 64937475606953630899444115)
      ·
        refine ⟨97406213410430446349166173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64937475606953630899444115 97406213410430446349166173)
        ·
          refine ⟨36527330028911417380937315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97406213410430446349166173 36527330028911417380937315)
          ·
            refine ⟨54790995043367126071405973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36527330028911417380937315 54790995043367126071405973)
            ·
              refine ⟨2568327892657834034597155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54790995043367126071405973 2568327892657834034597155)
              ·
                refine ⟨3852491838986751051895733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568327892657834034597155 3852491838986751051895733)
                ·
                  refine ⟨361171109905007911115225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3852491838986751051895733 361171109905007911115225)
                  ·
                    rfl

theorem cell21_1582601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_1582601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1582601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1582601 prefixEnd_1582601 := by exact prefixLift 1582601
  have htrace : WordTrace (prefixWord ++ tailWord_1582601) baseStart_1582601 baseEnd_1582601 := by
    simpa [prefixWord, tailWord_1582601, baseEnd_1582601] using wordTrace_append hprefix tailTrace_1582601
  have hstable : (prefixWord ++ tailWord_1582601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1582601).length < 2 ^ (prefixWord ++ tailWord_1582601).sum := by decide
  have hdescent : baseEnd_1582601 < baseStart_1582601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1582601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
