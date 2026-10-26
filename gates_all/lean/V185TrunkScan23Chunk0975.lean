import V185TrunkScan23Chunk0974

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5771350 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5771350 : Nat := 118140960795 + 5771350 * 2 ^ 59
def prefixEnd_5771350 : Nat := 4983230072969 + 3 ^ 40 * 5771350 * 2
def baseEnd_5771350 : Nat := 2963476575326099800283051

theorem tailTrace_5771350 : CollatzResearch.WordTrace tailWord_5771350 prefixEnd_5771350 2963476575326099800283051 := by
  unfold tailWord_5771350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156151727587005809503969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140332285094261395301375669 13156151727587005809503969)
  ·
    refine ⟨9867113795690254357127977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13156151727587005809503969 9867113795690254357127977)
    ·
      refine ⟨7400335346767690767845983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9867113795690254357127977 7400335346767690767845983)
      ·
        refine ⟨11100503020151536151768975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400335346767690767845983 11100503020151536151768975)
        ·
          refine ⟨16650754530227304227653463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100503020151536151768975 16650754530227304227653463)
          ·
            refine ⟨24976131795340956341480195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16650754530227304227653463 24976131795340956341480195)
            ·
              refine ⟨37464197693011434512220293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24976131795340956341480195 37464197693011434512220293)
              ·
                refine ⟨7024537067439643971041305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37464197693011434512220293 7024537067439643971041305)
                ·
                  refine ⟨5268402800579732978280979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024537067439643971041305 5268402800579732978280979)
                  ·
                    refine ⟨7902604200869599467421469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268402800579732978280979 7902604200869599467421469)
                    ·
                      refine ⟨2963476575326099800283051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902604200869599467421469 2963476575326099800283051)
                      ·
                        rfl

theorem cell23_5771350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5771350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771350 prefixEnd_5771350 := by exact prefixLift 5771350
  have htrace : WordTrace (prefixWord ++ tailWord_5771350) baseStart_5771350 baseEnd_5771350 := by
    simpa [prefixWord, tailWord_5771350, baseEnd_5771350] using wordTrace_append hprefix tailTrace_5771350
  have hstable : (prefixWord ++ tailWord_5771350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771350).length < 2 ^ (prefixWord ++ tailWord_5771350).sum := by decide
  have hdescent : baseEnd_5771350 < baseStart_5771350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771373 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 2, 2, 2]
def baseStart_5771373 : Nat := 118140960795 + 5771373 * 2 ^ 59
def prefixEnd_5771373 : Nat := 4983230072969 + 3 ^ 40 * 5771373 * 2
def baseEnd_5771373 : Nat := 2963488385381153210295445

theorem tailTrace_5771373 : CollatzResearch.WordTrace tailWord_5771373 prefixEnd_5771373 2963488385381153210295445 := by
  unfold tailWord_5771373
  simp only [CollatzResearch.WordTrace]
  refine ⟨210499266520308767880150773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140332844346872511920100515 210499266520308767880150773)
  ·
    refine ⟨19734306236278946988764135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210499266520308767880150773 19734306236278946988764135)
    ·
      refine ⟨29601459354418420483146203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19734306236278946988764135 29601459354418420483146203)
      ·
        refine ⟨44402189031627630724719305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29601459354418420483146203 44402189031627630724719305)
        ·
          refine ⟨33301641773720723043539479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44402189031627630724719305 33301641773720723043539479)
          ·
            refine ⟨49952462660581084565309219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33301641773720723043539479 49952462660581084565309219)
            ·
              refine ⟨74928693990871626847963829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49952462660581084565309219 74928693990871626847963829)
              ·
                refine ⟨7024565061644215016996609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74928693990871626847963829 7024565061644215016996609)
                ·
                  refine ⟨5268423796233161262747457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024565061644215016996609 5268423796233161262747457)
                  ·
                    refine ⟨3951317847174870947060593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268423796233161262747457 3951317847174870947060593)
                    ·
                      refine ⟨2963488385381153210295445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951317847174870947060593 2963488385381153210295445)
                      ·
                        rfl

theorem cell23_5771373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_5771373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771373 prefixEnd_5771373 := by exact prefixLift 5771373
  have htrace : WordTrace (prefixWord ++ tailWord_5771373) baseStart_5771373 baseEnd_5771373 := by
    simpa [prefixWord, tailWord_5771373, baseEnd_5771373] using wordTrace_append hprefix tailTrace_5771373
  have hstable : (prefixWord ++ tailWord_5771373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771373).length < 2 ^ (prefixWord ++ tailWord_5771373).sum := by decide
  have hdescent : baseEnd_5771373 < baseStart_5771373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771396 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 5]
def baseStart_5771396 : Nat := 118140960795 + 5771396 * 2 ^ 59
def prefixEnd_5771396 : Nat := 4983230072969 + 3 ^ 40 * 5771396 * 2
def baseEnd_5771396 : Nat := 329277799492911846700871

theorem tailTrace_5771396 : CollatzResearch.WordTrace tailWord_5771396 prefixEnd_5771396 329277799492911846700871 := by
  unfold tailWord_5771396
  simp only [CollatzResearch.WordTrace]
  refine ⟨105250052699612721404119021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140333403599483628538825361 105250052699612721404119021)
  ·
    refine ⟨39468769762354770526544633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105250052699612721404119021 39468769762354770526544633)
    ·
      refine ⟨29601577321766077894908475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39468769762354770526544633 29601577321766077894908475)
      ·
        refine ⟨44402365982649116842362713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29601577321766077894908475 44402365982649116842362713)
        ·
          refine ⟨33301774486986837631772035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44402365982649116842362713 33301774486986837631772035)
          ·
            refine ⟨49952661730480256447658053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33301774486986837631772035 49952661730480256447658053)
            ·
              refine ⟨9366124074465048083935885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49952661730480256447658053 9366124074465048083935885)
              ·
                refine ⟨3512296527924393031475957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9366124074465048083935885 3512296527924393031475957)
                ·
                  refine ⟨329277799492911846700871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3512296527924393031475957 329277799492911846700871)
                  ·
                    rfl

theorem cell23_5771396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_5771396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771396 prefixEnd_5771396 := by exact prefixLift 5771396
  have htrace : WordTrace (prefixWord ++ tailWord_5771396) baseStart_5771396 baseEnd_5771396 := by
    simpa [prefixWord, tailWord_5771396, baseEnd_5771396] using wordTrace_append hprefix tailTrace_5771396
  have hstable : (prefixWord ++ tailWord_5771396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771396).length < 2 ^ (prefixWord ++ tailWord_5771396).sum := by decide
  have hdescent : baseEnd_5771396 < baseStart_5771396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771449 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5771449 : Nat := 118140960795 + 5771449 * 2 ^ 59
def prefixEnd_5771449 : Nat := 4983230072969 + 3 ^ 40 * 5771449 * 2
def baseEnd_5771449 : Nat := 2963527409910894912945095

theorem tailTrace_5771449 : CollatzResearch.WordTrace tailWord_5771449 prefixEnd_5771449 2963527409910894912945095 := by
  unfold tailWord_5771449
  simp only [CollatzResearch.WordTrace]
  refine ⟨210502038468033432859917401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140334692312022288573278267 210502038468033432859917401)
  ·
    refine ⟨157876528851025074644938051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210502038468033432859917401 157876528851025074644938051)
    ·
      refine ⟨236814793276537611967407077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157876528851025074644938051 236814793276537611967407077)
      ·
        refine ⟨44402773739350802243888827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236814793276537611967407077 44402773739350802243888827)
        ·
          refine ⟨66604160609026203365833241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44402773739350802243888827 66604160609026203365833241)
          ·
            refine ⟨49953120456769652524374931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66604160609026203365833241 49953120456769652524374931)
            ·
              refine ⟨74929680685154478786562397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49953120456769652524374931 74929680685154478786562397)
              ·
                refine ⟨28098630256932929544960899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74929680685154478786562397 28098630256932929544960899)
                ·
                  refine ⟨42147945385399394317441349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28098630256932929544960899 42147945385399394317441349)
                  ·
                    refine ⟨7902739759762386434520253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42147945385399394317441349 7902739759762386434520253)
                    ·
                      refine ⟨2963527409910894912945095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902739759762386434520253 2963527409910894912945095)
                      ·
                        rfl

theorem cell23_5771449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5771449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771449 prefixEnd_5771449 := by exact prefixLift 5771449
  have htrace : WordTrace (prefixWord ++ tailWord_5771449) baseStart_5771449 baseEnd_5771449 := by
    simpa [prefixWord, tailWord_5771449, baseEnd_5771449] using wordTrace_append hprefix tailTrace_5771449
  have hstable : (prefixWord ++ tailWord_5771449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771449).length < 2 ^ (prefixWord ++ tailWord_5771449).sum := by decide
  have hdescent : baseEnd_5771449 < baseStart_5771449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771466 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_5771466 : Nat := 118140960795 + 5771466 * 2 ^ 59
def prefixEnd_5771466 : Nat := 4983230072969 + 3 ^ 40 * 5771466 * 2
def baseEnd_5771466 : Nat := 2963536139082021346432517

theorem tailTrace_5771466 : CollatzResearch.WordTrace tailWord_5771466 prefixEnd_5771466 2963536139082021346432517 := by
  unfold tailWord_5771466
  simp only [CollatzResearch.WordTrace]
  refine ⟨52625664627242961190821563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140335105672647896508857501 52625664627242961190821563)
  ·
    refine ⟨78938496940864441786232345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52625664627242961190821563 78938496940864441786232345)
    ·
      refine ⟨59203872705648331339674259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78938496940864441786232345 59203872705648331339674259)
      ·
        refine ⟨88805809058472497009511389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59203872705648331339674259 88805809058472497009511389)
        ·
          refine ⟨33302178396927186378566771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88805809058472497009511389 33302178396927186378566771)
          ·
            refine ⟨49953267595390779567850157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33302178396927186378566771 49953267595390779567850157)
            ·
              refine ⟨18732475348271542337943809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49953267595390779567850157 18732475348271542337943809)
              ·
                refine ⟨14049356511203656753457857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18732475348271542337943809 14049356511203656753457857)
                ·
                  refine ⟨10537017383402742565093393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14049356511203656753457857 10537017383402742565093393)
                  ·
                    refine ⟨7902763037552056923820045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10537017383402742565093393 7902763037552056923820045)
                    ·
                      refine ⟨2963536139082021346432517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902763037552056923820045 2963536139082021346432517)
                      ·
                        rfl

theorem cell23_5771466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_5771466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771466 prefixEnd_5771466 := by exact prefixLift 5771466
  have htrace : WordTrace (prefixWord ++ tailWord_5771466) baseStart_5771466 baseEnd_5771466 := by
    simpa [prefixWord, tailWord_5771466, baseEnd_5771466] using wordTrace_append hprefix tailTrace_5771466
  have hstable : (prefixWord ++ tailWord_5771466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771466).length < 2 ^ (prefixWord ++ tailWord_5771466).sum := by decide
  have hdescent : baseEnd_5771466 < baseStart_5771466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771499 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 3, 5]
def baseStart_5771499 : Nat := 118140960795 + 5771499 * 2 ^ 59
def prefixEnd_5771499 : Nat := 4983230072969 + 3 ^ 40 * 5771499 * 2
def baseEnd_5771499 : Nat := 987851027981206572439955

theorem tailTrace_5771499 : CollatzResearch.WordTrace tailWord_5771499 prefixEnd_5771499 987851027981206572439955 := by
  unfold tailWord_5771499
  simp only [CollatzResearch.WordTrace]
  refine ⟨210503862117852291399237551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140335908078568194266158367 210503862117852291399237551)
  ·
    refine ⟨315755793176778437098856327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210503862117852291399237551 315755793176778437098856327)
    ·
      refine ⟨473633689765167655648284491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315755793176778437098856327 473633689765167655648284491)
      ·
        refine ⟨710450534647751483472426737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473633689765167655648284491 710450534647751483472426737)
        ·
          refine ⟨532837900985813612604320053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710450534647751483472426737 532837900985813612604320053)
          ·
            refine ⟨49953553217420026181655005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 532837900985813612604320053 49953553217420026181655005)
            ·
              refine ⟨18732582456532509818120627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49953553217420026181655005 18732582456532509818120627)
              ·
                refine ⟨28098873684798764727180941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18732582456532509818120627 28098873684798764727180941)
                ·
                  refine ⟨10537077631799536772692853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28098873684798764727180941 10537077631799536772692853)
                  ·
                    refine ⟨987851027981206572439955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10537077631799536772692853 987851027981206572439955)
                    ·
                      rfl

theorem cell23_5771499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 5].length) (baseStart_5771499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771499 prefixEnd_5771499 := by exact prefixLift 5771499
  have htrace : WordTrace (prefixWord ++ tailWord_5771499) baseStart_5771499 baseEnd_5771499 := by
    simpa [prefixWord, tailWord_5771499, baseEnd_5771499] using wordTrace_append hprefix tailTrace_5771499
  have hstable : (prefixWord ++ tailWord_5771499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771499).length < 2 ^ (prefixWord ++ tailWord_5771499).sum := by decide
  have hdescent : baseEnd_5771499 < baseStart_5771499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771524 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5771524 : Nat := 118140960795 + 5771524 * 2 ^ 59
def prefixEnd_5771524 : Nat := 4983230072969 + 3 ^ 40 * 5771524 * 2
def baseEnd_5771524 : Nat := 987855306986660706502417

theorem tailTrace_5771524 : CollatzResearch.WordTrace tailWord_5771524 prefixEnd_5771524 987855306986660706502417 := by
  unfold tailWord_5771524
  simp only [CollatzResearch.WordTrace]
  refine ⟨105252386971380860334448813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140336515961841147112598417 105252386971380860334448813)
  ·
    refine ⟨39469645114267822625418305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105252386971380860334448813 39469645114267822625418305)
    ·
      refine ⟨29602233835700866969063729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39469645114267822625418305 29602233835700866969063729)
      ·
        refine ⟨22201675376775650226797797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29602233835700866969063729 22201675376775650226797797)
        ·
          refine ⟨4162814133145434417524587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22201675376775650226797797 4162814133145434417524587)
          ·
            refine ⟨6244221199718151626286881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162814133145434417524587 6244221199718151626286881)
            ·
              refine ⟨4683165899788613719715161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244221199718151626286881 4683165899788613719715161)
              ·
                refine ⟨3512374424841460289786371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683165899788613719715161 3512374424841460289786371)
                ·
                  refine ⟨5268561637262190434679557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512374424841460289786371 5268561637262190434679557)
                  ·
                    refine ⟨987855306986660706502417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268561637262190434679557 987855306986660706502417)
                    ·
                      rfl

theorem cell23_5771524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5771524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771524 prefixEnd_5771524 := by exact prefixLift 5771524
  have htrace : WordTrace (prefixWord ++ tailWord_5771524) baseStart_5771524 baseEnd_5771524 := by
    simpa [prefixWord, tailWord_5771524, baseEnd_5771524] using wordTrace_append hprefix tailTrace_5771524
  have hstable : (prefixWord ++ tailWord_5771524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771524).length < 2 ^ (prefixWord ++ tailWord_5771524).sum := by decide
  have hdescent : baseEnd_5771524 < baseStart_5771524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771539 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5]
def baseStart_5771539 : Nat := 118140960795 + 5771539 * 2 ^ 59
def prefixEnd_5771539 : Nat := 4983230072969 + 3 ^ 40 * 5771539 * 2
def baseEnd_5771539 : Nat := 2963573623169799560819681

theorem tailTrace_5771539 : CollatzResearch.WordTrace tailWord_5771539 prefixEnd_5771539 2963573623169799560819681 := by
  unfold tailWord_5771539
  simp only [CollatzResearch.WordTrace]
  refine ⟨210505321037707378230693671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140336880691804918820462447 210505321037707378230693671)
  ·
    refine ⟨315757981556561067346040507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210505321037707378230693671 315757981556561067346040507)
    ·
      refine ⟨473636972334841601019060761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315757981556561067346040507 473636972334841601019060761)
      ·
        refine ⟨355227729251131200764295571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473636972334841601019060761 355227729251131200764295571)
        ·
          refine ⟨532841593876696801146443357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355227729251131200764295571 532841593876696801146443357)
          ·
            refine ⟨199815597703761300429916259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 532841593876696801146443357 199815597703761300429916259)
            ·
              refine ⟨299723396555641950644874389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199815597703761300429916259 299723396555641950644874389)
              ·
                refine ⟨14049534213545716436478487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299723396555641950644874389 14049534213545716436478487)
                ·
                  refine ⟨21074301320318574654717731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14049534213545716436478487 21074301320318574654717731)
                  ·
                    refine ⟨31611451980477861982076597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21074301320318574654717731 31611451980477861982076597)
                    ·
                      refine ⟨2963573623169799560819681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31611451980477861982076597 2963573623169799560819681)
                      ·
                        rfl

theorem cell23_5771539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_5771539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771539 prefixEnd_5771539 := by exact prefixLift 5771539
  have htrace : WordTrace (prefixWord ++ tailWord_5771539) baseStart_5771539 baseEnd_5771539 := by
    simpa [prefixWord, tailWord_5771539, baseEnd_5771539] using wordTrace_append hprefix tailTrace_5771539
  have hstable : (prefixWord ++ tailWord_5771539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771539).length < 2 ^ (prefixWord ++ tailWord_5771539).sum := by decide
  have hdescent : baseEnd_5771539 < baseStart_5771539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771553 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_5771553 : Nat := 118140960795 + 5771553 * 2 ^ 59
def prefixEnd_5771553 : Nat := 4983230072969 + 3 ^ 40 * 5771553 * 2
def baseEnd_5771553 : Nat := 2963580811898962506044617

theorem tailTrace_5771553 : CollatzResearch.WordTrace tailWord_5771553 prefixEnd_5771553 2963580811898962506044617 := by
  unfold tailWord_5771553
  simp only [CollatzResearch.WordTrace]
  refine ⟨210505831659656658621703313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140337221106437772414468875 210505831659656658621703313)
  ·
    refine ⟨157879373744742493966277485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210505831659656658621703313 157879373744742493966277485)
    ·
      refine ⟨59204765154278435237354057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157879373744742493966277485 59204765154278435237354057)
      ·
        refine ⟨44403573865708826428015543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59204765154278435237354057 44403573865708826428015543)
        ·
          refine ⟨66605360798563239642023315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44403573865708826428015543 66605360798563239642023315)
          ·
            refine ⟨99908041197844859463034973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66605360798563239642023315 99908041197844859463034973)
            ·
              refine ⟨37465515449191822298638115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99908041197844859463034973 37465515449191822298638115)
              ·
                refine ⟨56198273173787733447957173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37465515449191822298638115 56198273173787733447957173)
                ·
                  refine ⟨5268588110042600010745985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56198273173787733447957173 5268588110042600010745985)
                  ·
                    refine ⟨3951441082531950008059489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268588110042600010745985 3951441082531950008059489)
                    ·
                      refine ⟨2963580811898962506044617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951441082531950008059489 2963580811898962506044617)
                      ·
                        rfl

theorem cell23_5771553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_5771553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771553 prefixEnd_5771553 := by exact prefixLift 5771553
  have htrace : WordTrace (prefixWord ++ tailWord_5771553) baseStart_5771553 baseEnd_5771553 := by
    simpa [prefixWord, tailWord_5771553, baseEnd_5771553] using wordTrace_append hprefix tailTrace_5771553
  have hstable : (prefixWord ++ tailWord_5771553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771553).length < 2 ^ (prefixWord ++ tailWord_5771553).sum := by decide
  have hdescent : baseEnd_5771553 < baseStart_5771553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771557 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_5771557 : Nat := 118140960795 + 5771557 * 2 ^ 59
def prefixEnd_5771557 : Nat := 4983230072969 + 3 ^ 40 * 5771557 * 2
def baseEnd_5771557 : Nat := 2963582865821580490394599

theorem tailTrace_5771557 : CollatzResearch.WordTrace tailWord_5771557 prefixEnd_5771557 2963582865821580490394599 := by
  unfold tailWord_5771557
  simp only [CollatzResearch.WordTrace]
  refine ⟨210505977551642167304848925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140337318367761444869899283 210505977551642167304848925)
  ·
    refine ⟨78939741581865812739318347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210505977551642167304848925 78939741581865812739318347)
    ·
      refine ⟨118409612372798719108977521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78939741581865812739318347 118409612372798719108977521)
      ·
        refine ⟨88807209279599039331733141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118409612372798719108977521 88807209279599039331733141)
        ·
          refine ⟨4162837934981204968674991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88807209279599039331733141 4162837934981204968674991)
          ·
            refine ⟨6244256902471807453012487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162837934981204968674991 6244256902471807453012487)
            ·
              refine ⟨9366385353707711179518731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244256902471807453012487 9366385353707711179518731)
              ·
                refine ⟨14049578030561566769278097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9366385353707711179518731 14049578030561566769278097)
                ·
                  refine ⟨10537183522921175076958573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14049578030561566769278097 10537183522921175076958573)
                  ·
                    refine ⟨3951443821095440653859465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10537183522921175076958573 3951443821095440653859465)
                    ·
                      refine ⟨2963582865821580490394599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951443821095440653859465 2963582865821580490394599)
                      ·
                        rfl

theorem cell23_5771557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_5771557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771557 prefixEnd_5771557 := by exact prefixLift 5771557
  have htrace : WordTrace (prefixWord ++ tailWord_5771557) baseStart_5771557 baseEnd_5771557 := by
    simpa [prefixWord, tailWord_5771557, baseEnd_5771557] using wordTrace_append hprefix tailTrace_5771557
  have hstable : (prefixWord ++ tailWord_5771557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771557).length < 2 ^ (prefixWord ++ tailWord_5771557).sum := by decide
  have hdescent : baseEnd_5771557 < baseStart_5771557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771573 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_5771573 : Nat := 118140960795 + 5771573 * 2 ^ 59
def prefixEnd_5771573 : Nat := 4983230072969 + 3 ^ 40 * 5771573 * 2
def baseEnd_5771573 : Nat := 2963591081512052427794525

theorem tailTrace_5771573 : CollatzResearch.WordTrace tailWord_5771573 prefixEnd_5771573 2963591081512052427794525 := by
  unfold tailWord_5771573
  simp only [CollatzResearch.WordTrace]
  refine ⟨210506561119584202037431373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140337707413056134691620915 210506561119584202037431373)
  ·
    refine ⟨78939960419844075764036765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210506561119584202037431373 78939960419844075764036765)
    ·
      refine ⟨29602485157441528411513787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78939960419844075764036765 29602485157441528411513787)
      ·
        refine ⟨44403727736162292617270681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29602485157441528411513787 44403727736162292617270681)
        ·
          refine ⟨33302795802121719462953011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44403727736162292617270681 33302795802121719462953011)
          ·
            refine ⟨49954193703182579194429517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33302795802121719462953011 49954193703182579194429517)
            ·
              refine ⟨18732822638693467197911069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49954193703182579194429517 18732822638693467197911069)
              ·
                refine ⟨7024808489510050199216651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18732822638693467197911069 7024808489510050199216651)
                ·
                  refine ⟨10537212734265075298824977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024808489510050199216651 10537212734265075298824977)
                  ·
                    refine ⟨7902909550698806474118733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10537212734265075298824977 7902909550698806474118733)
                    ·
                      refine ⟨2963591081512052427794525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7902909550698806474118733 2963591081512052427794525)
                      ·
                        rfl

theorem cell23_5771573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_5771573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771573 prefixEnd_5771573 := by exact prefixLift 5771573
  have htrace : WordTrace (prefixWord ++ tailWord_5771573) baseStart_5771573 baseEnd_5771573 := by
    simpa [prefixWord, tailWord_5771573, baseEnd_5771573] using wordTrace_append hprefix tailTrace_5771573
  have hstable : (prefixWord ++ tailWord_5771573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771573).length < 2 ^ (prefixWord ++ tailWord_5771573).sum := by decide
  have hdescent : baseEnd_5771573 < baseStart_5771573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771638 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5771638 : Nat := 118140960795 + 5771638 * 2 ^ 59
def prefixEnd_5771638 : Nat := 4983230072969 + 3 ^ 40 * 5771638 * 2
def baseEnd_5771638 : Nat := 2963624457754594673481727

theorem tailTrace_5771638 : CollatzResearch.WordTrace tailWord_5771638 prefixEnd_5771638 2963624457754594673481727 := by
  unfold tailWord_5771638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156808241521794883659223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140339287909565812092365045 13156808241521794883659223)
  ·
    refine ⟨19735212362282692325488835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13156808241521794883659223 19735212362282692325488835)
    ·
      refine ⟨29602818543424038488233253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19735212362282692325488835 29602818543424038488233253)
      ·
        refine ⟨5550528476892007216543735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29602818543424038488233253 5550528476892007216543735)
        ·
          refine ⟨8325792715338010824815603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550528476892007216543735 8325792715338010824815603)
          ·
            refine ⟨12488689073007016237223405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325792715338010824815603 12488689073007016237223405)
            ·
              refine ⟨4683258402377631088958777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12488689073007016237223405 4683258402377631088958777)
              ·
                refine ⟨3512443801783223316719083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683258402377631088958777 3512443801783223316719083)
                ·
                  refine ⟨5268665702674834975078625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512443801783223316719083 5268665702674834975078625)
                  ·
                    refine ⟨3951499277006126231308969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5268665702674834975078625 3951499277006126231308969)
                    ·
                      refine ⟨2963624457754594673481727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951499277006126231308969 2963624457754594673481727)
                      ·
                        rfl

theorem cell23_5771638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5771638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771638 prefixEnd_5771638 := by exact prefixLift 5771638
  have htrace : WordTrace (prefixWord ++ tailWord_5771638) baseStart_5771638 baseEnd_5771638 := by
    simpa [prefixWord, tailWord_5771638, baseEnd_5771638] using wordTrace_append hprefix tailTrace_5771638
  have hstable : (prefixWord ++ tailWord_5771638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771638).length < 2 ^ (prefixWord ++ tailWord_5771638).sum := by decide
  have hdescent : baseEnd_5771638 < baseStart_5771638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771639 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_5771639 : Nat := 118140960795 + 5771639 * 2 ^ 59
def prefixEnd_5771639 : Nat := 4983230072969 + 3 ^ 40 * 5771639 * 2
def baseEnd_5771639 : Nat := 2963624971235249169569221

theorem tailTrace_5771639 : CollatzResearch.WordTrace tailWord_5771639 prefixEnd_5771639 2963624971235249169569221 := by
  unfold tailWord_5771639
  simp only [CollatzResearch.WordTrace]
  refine ⟨210508968337345095309333971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140339312224896730206222647 210508968337345095309333971)
  ·
    refine ⟨315763452506017642964000957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210508968337345095309333971 315763452506017642964000957)
    ·
      refine ⟨118411294689756616111500359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315763452506017642964000957 118411294689756616111500359)
      ·
        refine ⟨177616942034634924167250539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118411294689756616111500359 177616942034634924167250539)
        ·
          refine ⟨266425413051952386250875809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177616942034634924167250539 266425413051952386250875809)
          ·
            refine ⟨199819059788964289688156857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266425413051952386250875809 199819059788964289688156857)
            ·
              refine ⟨149864294841723217266117643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199819059788964289688156857 149864294841723217266117643)
              ·
                refine ⟨224796442262584825899176465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149864294841723217266117643 224796442262584825899176465)
                ·
                  refine ⟨168597331696938619424382349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224796442262584825899176465 168597331696938619424382349)
                  ·
                    refine ⟨63223999386351982284143381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168597331696938619424382349 63223999386351982284143381)
                    ·
                      refine ⟨2963624971235249169569221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63223999386351982284143381 2963624971235249169569221)
                      ·
                        rfl

theorem cell23_5771639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_5771639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771639 prefixEnd_5771639 := by exact prefixLift 5771639
  have htrace : WordTrace (prefixWord ++ tailWord_5771639) baseStart_5771639 baseEnd_5771639 := by
    simpa [prefixWord, tailWord_5771639, baseEnd_5771639] using wordTrace_append hprefix tailTrace_5771639
  have hstable : (prefixWord ++ tailWord_5771639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771639).length < 2 ^ (prefixWord ++ tailWord_5771639).sum := by decide
  have hdescent : baseEnd_5771639 < baseStart_5771639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771656 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5771656 : Nat := 118140960795 + 5771656 * 2 ^ 59
def prefixEnd_5771656 : Nat := 4983230072969 + 3 ^ 40 * 5771656 * 2
def baseEnd_5771656 : Nat := 2963633700406375603056643

theorem tailTrace_5771656 : CollatzResearch.WordTrace tailWord_5771656 prefixEnd_5771656 2963633700406375603056643 := by
  unfold tailWord_5771656
  simp only [CollatzResearch.WordTrace]
  refine ⟨105254794189141753606351411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140339725585522338141801881 105254794189141753606351411)
  ·
    refine ⟨157882191283712630409527117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105254794189141753606351411 157882191283712630409527117)
    ·
      refine ⟨59205821731392236403572669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157882191283712630409527117 59205821731392236403572669)
      ·
        refine ⟨22202183149272088651339751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59205821731392236403572669 22202183149272088651339751)
        ·
          refine ⟨33303274723908132977009627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22202183149272088651339751 33303274723908132977009627)
          ·
            refine ⟨49954912085862199465514441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33303274723908132977009627 49954912085862199465514441)
            ·
              refine ⟨37466184064396649599135831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49954912085862199465514441 37466184064396649599135831)
              ·
                refine ⟨56199276096594974398703747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37466184064396649599135831 56199276096594974398703747)
                ·
                  refine ⟨84298914144892461598055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56199276096594974398703747 84298914144892461598055621)
                  ·
                    refine ⟨15806046402167336549635429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84298914144892461598055621 15806046402167336549635429)
                    ·
                      refine ⟨2963633700406375603056643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15806046402167336549635429 2963633700406375603056643)
                      ·
                        rfl

theorem cell23_5771656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5771656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771656 prefixEnd_5771656 := by exact prefixLift 5771656
  have htrace : WordTrace (prefixWord ++ tailWord_5771656) baseStart_5771656 baseEnd_5771656 := by
    simpa [prefixWord, tailWord_5771656, baseEnd_5771656] using wordTrace_append hprefix tailTrace_5771656
  have hstable : (prefixWord ++ tailWord_5771656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771656).length < 2 ^ (prefixWord ++ tailWord_5771656).sum := by decide
  have hdescent : baseEnd_5771656 < baseStart_5771656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771703 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_5771703 : Nat := 118140960795 + 5771703 * 2 ^ 59
def prefixEnd_5771703 : Nat := 4983230072969 + 3 ^ 40 * 5771703 * 2
def baseEnd_5771703 : Nat := 2963657833997136919168927

theorem tailTrace_5771703 : CollatzResearch.WordTrace tailWord_5771703 prefixEnd_5771703 2963657833997136919168927 := by
  unfold tailWord_5771703
  simp only [CollatzResearch.WordTrace]
  refine ⟨210511302609113234239663763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140340868406075489493109175 210511302609113234239663763)
  ·
    refine ⟨315766953913669851359495645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210511302609113234239663763 315766953913669851359495645)
    ·
      refine ⟨118412607717626194259810867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315766953913669851359495645 118412607717626194259810867)
      ·
        refine ⟨177618911576439291389716301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118412607717626194259810867 177618911576439291389716301)
        ·
          refine ⟨66607091841164734271143613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177618911576439291389716301 66607091841164734271143613)
          ·
            refine ⟨24977659440436775351678855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66607091841164734271143613 24977659440436775351678855)
            ·
              refine ⟨37466489160655163027518283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24977659440436775351678855 37466489160655163027518283)
              ·
                refine ⟨56199733740982744541277425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37466489160655163027518283 56199733740982744541277425)
                ·
                  refine ⟨42149800305737058405958069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56199733740982744541277425 42149800305737058405958069)
                  ·
                    refine ⟨3951543778662849225558569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42149800305737058405958069 3951543778662849225558569)
                    ·
                      refine ⟨2963657833997136919168927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951543778662849225558569 2963657833997136919168927)
                      ·
                        rfl

theorem cell23_5771703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_5771703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771703 prefixEnd_5771703 := by exact prefixLift 5771703
  have htrace : WordTrace (prefixWord ++ tailWord_5771703) baseStart_5771703 baseEnd_5771703 := by
    simpa [prefixWord, tailWord_5771703, baseEnd_5771703] using wordTrace_append hprefix tailTrace_5771703
  have hstable : (prefixWord ++ tailWord_5771703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771703).length < 2 ^ (prefixWord ++ tailWord_5771703).sum := by decide
  have hdescent : baseEnd_5771703 < baseStart_5771703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771730 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_5771730 : Nat := 118140960795 + 5771730 * 2 ^ 59
def prefixEnd_5771730 : Nat := 4983230072969 + 3 ^ 40 * 5771730 * 2
def baseEnd_5771730 : Nat := 987890565991602771177101

theorem tailTrace_5771730 : CollatzResearch.WordTrace tailWord_5771730 prefixEnd_5771730 987890565991602771177101 := by
  unfold tailWord_5771730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52628071845003854462724161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140341524920010278567264429 52628071845003854462724161)
  ·
    refine ⟨39471053883752890847043121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52628071845003854462724161 39471053883752890847043121)
    ·
      refine ⟨29603290412814668135282341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39471053883752890847043121 29603290412814668135282341)
      ·
        refine ⟨5550616952402750275365439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29603290412814668135282341 5550616952402750275365439)
        ·
          refine ⟨8325925428604125413048159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550616952402750275365439 8325925428604125413048159)
          ·
            refine ⟨12488888142906188119572239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325925428604125413048159 12488888142906188119572239)
            ·
              refine ⟨18733332214359282179358359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12488888142906188119572239 18733332214359282179358359)
              ·
                refine ⟨28099998321538923269037539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18733332214359282179358359 28099998321538923269037539)
                ·
                  refine ⟨42149997482308384903556309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28099998321538923269037539 42149997482308384903556309)
                  ·
                    refine ⟨987890565991602771177101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42149997482308384903556309 987890565991602771177101)
                    ·
                      rfl

theorem cell23_5771730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_5771730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771730 prefixEnd_5771730 := by exact prefixLift 5771730
  have htrace : WordTrace (prefixWord ++ tailWord_5771730) baseStart_5771730 baseEnd_5771730 := by
    simpa [prefixWord, tailWord_5771730, baseEnd_5771730] using wordTrace_append hprefix tailTrace_5771730
  have hstable : (prefixWord ++ tailWord_5771730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771730).length < 2 ^ (prefixWord ++ tailWord_5771730).sum := by decide
  have hdescent : baseEnd_5771730 < baseStart_5771730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771733 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_5771733 : Nat := 118140960795 + 5771733 * 2 ^ 59
def prefixEnd_5771733 : Nat := 4983230072969 + 3 ^ 40 * 5771733 * 2
def baseEnd_5771733 : Nat := 2963673238416771801793789

theorem tailTrace_5771733 : CollatzResearch.WordTrace tailWord_5771733 prefixEnd_5771733 2963673238416771801793789 := by
  unfold tailWord_5771733
  simp only [CollatzResearch.WordTrace]
  refine ⟨210512396799004549363255853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140341597866003032908837235 210512396799004549363255853)
  ·
    refine ⟨78942148799626706011220945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210512396799004549363255853 78942148799626706011220945)
    ·
      refine ⟨59206611599720029508415709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78942148799626706011220945 59206611599720029508415709)
      ·
        refine ⟨22202479349895011065655891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59206611599720029508415709 22202479349895011065655891)
        ·
          refine ⟨33303719024842516598483837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22202479349895011065655891 33303719024842516598483837)
          ·
            refine ⟨12488894634315943724431439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33303719024842516598483837 12488894634315943724431439)
            ·
              refine ⟨18733341951473915586647159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12488894634315943724431439 18733341951473915586647159)
              ·
                refine ⟨28100012927210873379970739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18733341951473915586647159 28100012927210873379970739)
                ·
                  refine ⟨42150019390816310069956109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28100012927210873379970739 42150019390816310069956109)
                  ·
                    refine ⟨15806257271556116276233541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42150019390816310069956109 15806257271556116276233541)
                    ·
                      refine ⟨2963673238416771801793789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15806257271556116276233541 2963673238416771801793789)
                      ·
                        rfl

theorem cell23_5771733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_5771733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771733 prefixEnd_5771733 := by exact prefixLift 5771733
  have htrace : WordTrace (prefixWord ++ tailWord_5771733) baseStart_5771733 baseEnd_5771733 := by
    simpa [prefixWord, tailWord_5771733, baseEnd_5771733] using wordTrace_append hprefix tailTrace_5771733
  have hstable : (prefixWord ++ tailWord_5771733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771733).length < 2 ^ (prefixWord ++ tailWord_5771733).sum := by decide
  have hdescent : baseEnd_5771733 < baseStart_5771733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771756 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 8]
def baseStart_5771756 : Nat := 118140960795 + 5771756 * 2 ^ 59
def prefixEnd_5771756 : Nat := 4983230072969 + 3 ^ 40 * 5771756 * 2
def baseEnd_5771756 : Nat := 329298338719091690200687

theorem tailTrace_5771756 : CollatzResearch.WordTrace tailWord_5771756 prefixEnd_5771756 329298338719091690200687 := by
  unfold tailWord_5771756
  simp only [CollatzResearch.WordTrace]
  refine ⟨105256617838960612145671561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140342157118614149527562081 105256617838960612145671561)
  ·
    refine ⟨78942463379220459109253671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105256617838960612145671561 78942463379220459109253671)
    ·
      refine ⟨118413695068830688663880507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78942463379220459109253671 118413695068830688663880507)
      ·
        refine ⟨177620542603246032995820761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118413695068830688663880507 177620542603246032995820761)
        ·
          refine ⟨133215406952434524746865571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177620542603246032995820761 133215406952434524746865571)
          ·
            refine ⟨199823110428651787120298357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133215406952434524746865571 199823110428651787120298357)
            ·
              refine ⟨18733416602686105042527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199823110428651787120298357 18733416602686105042527971)
              ·
                refine ⟨28100124904029157563791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18733416602686105042527971 28100124904029157563791957)
                ·
                  refine ⟨329298338719091690200687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28100124904029157563791957 329298338719091690200687)
                  ·
                    rfl

theorem cell23_5771756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 8].length) (baseStart_5771756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771756 prefixEnd_5771756 := by exact prefixLift 5771756
  have htrace : WordTrace (prefixWord ++ tailWord_5771756) baseStart_5771756 baseEnd_5771756 := by
    simpa [prefixWord, tailWord_5771756, baseEnd_5771756] using wordTrace_append hprefix tailTrace_5771756
  have hstable : (prefixWord ++ tailWord_5771756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771756).length < 2 ^ (prefixWord ++ tailWord_5771756).sum := by decide
  have hdescent : baseEnd_5771756 < baseStart_5771756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771760 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 1, 4]
def baseStart_5771760 : Nat := 118140960795 + 5771760 * 2 ^ 59
def prefixEnd_5771760 : Nat := 4983230072969 + 3 ^ 40 * 5771760 * 2
def baseEnd_5771760 : Nat := 987895700798147732052055

theorem tailTrace_5771760 : CollatzResearch.WordTrace tailWord_5771760 prefixEnd_5771760 987895700798147732052055 := by
  unfold tailWord_5771760
  simp only [CollatzResearch.WordTrace]
  refine ⟨105256690784953366487244367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140342254379937821982992489 105256690784953366487244367)
  ·
    refine ⟨157885036177430049730866551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105256690784953366487244367 157885036177430049730866551)
    ·
      refine ⟨236827554266145074596299827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157885036177430049730866551 236827554266145074596299827)
      ·
        refine ⟨355241331399217611894449741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236827554266145074596299827 355241331399217611894449741)
        ·
          refine ⟨133215499274706604460418653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355241331399217611894449741 133215499274706604460418653)
          ·
            refine ⟨49955812228014976672656995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133215499274706604460418653 49955812228014976672656995)
            ·
              refine ⟨74933718342022465008985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49955812228014976672656995 74933718342022465008985493)
              ·
                refine ⟨3512518047282303047296195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74933718342022465008985493 3512518047282303047296195)
                ·
                  refine ⟨5268777070923454570944293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512518047282303047296195 5268777070923454570944293)
                  ·
                    refine ⟨987895700798147732052055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268777070923454570944293 987895700798147732052055)
                    ·
                      rfl

theorem cell23_5771760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 1, 4].length) (baseStart_5771760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771760 prefixEnd_5771760 := by exact prefixLift 5771760
  have htrace : WordTrace (prefixWord ++ tailWord_5771760) baseStart_5771760 baseEnd_5771760 := by
    simpa [prefixWord, tailWord_5771760, baseEnd_5771760] using wordTrace_append hprefix tailTrace_5771760
  have hstable : (prefixWord ++ tailWord_5771760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771760).length < 2 ^ (prefixWord ++ tailWord_5771760).sum := by decide
  have hdescent : baseEnd_5771760 < baseStart_5771760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771833 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 6]
def baseStart_5771833 : Nat := 118140960795 + 5771833 * 2 ^ 59
def prefixEnd_5771833 : Nat := 4983230072969 + 3 ^ 40 * 5771833 * 2
def baseEnd_5771833 : Nat := 987908195494073803514443

theorem tailTrace_5771833 : CollatzResearch.WordTrace tailWord_5771833 prefixEnd_5771833 987908195494073803514443 := by
  unfold tailWord_5771833
  simp only [CollatzResearch.WordTrace]
  refine ⟨210516044098642266441896153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140344029399094844294597435 210516044098642266441896153)
  ·
    refine ⟨157887033073981699831422115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210516044098642266441896153 157887033073981699831422115)
    ·
      refine ⟨236830549610972549747133173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157887033073981699831422115 236830549610972549747133173)
      ·
        refine ⟨22202864026028676538793735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 236830549610972549747133173 22202864026028676538793735)
        ·
          refine ⟨33304296039043014808190603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22202864026028676538793735 33304296039043014808190603)
          ·
            refine ⟨49956444058564522212285905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33304296039043014808190603 49956444058564522212285905)
            ·
              refine ⟨37467333043923391659214429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49956444058564522212285905 37467333043923391659214429)
              ·
                refine ⟨14050249891471271872205411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37467333043923391659214429 14050249891471271872205411)
                ·
                  refine ⟨21075374837206907808308117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14050249891471271872205411 21075374837206907808308117)
                  ·
                    refine ⟨987908195494073803514443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21075374837206907808308117 987908195494073803514443)
                    ·
                      rfl

theorem cell23_5771833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_5771833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771833 prefixEnd_5771833 := by exact prefixLift 5771833
  have htrace : WordTrace (prefixWord ++ tailWord_5771833) baseStart_5771833 baseEnd_5771833 := by
    simpa [prefixWord, tailWord_5771833, baseEnd_5771833] using wordTrace_append hprefix tailTrace_5771833
  have hstable : (prefixWord ++ tailWord_5771833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771833).length < 2 ^ (prefixWord ++ tailWord_5771833).sum := by decide
  have hdescent : baseEnd_5771833 < baseStart_5771833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771837 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_5771837 : Nat := 118140960795 + 5771837 * 2 ^ 59
def prefixEnd_5771837 : Nat := 4983230072969 + 3 ^ 40 * 5771837 * 2
def baseEnd_5771837 : Nat := 987908880134946464964437

theorem tailTrace_5771837 : CollatzResearch.WordTrace tailWord_5771837 prefixEnd_5771837 987908880134946464964437 := by
  unfold tailWord_5771837
  simp only [CollatzResearch.WordTrace]
  refine ⟨210516189990627775125041765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140344126660418516750027843 210516189990627775125041765)
  ·
    refine ⟨39471785623242707835945331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210516189990627775125041765 39471785623242707835945331)
    ·
      refine ⟨59207678434864061753917997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39471785623242707835945331 59207678434864061753917997)
      ·
        refine ⟨22202879413074023157719249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59207678434864061753917997 22202879413074023157719249)
        ·
          refine ⟨16652159559805517368289437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22202879413074023157719249 16652159559805517368289437)
          ·
            refine ⟨6244559834927069013108539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16652159559805517368289437 6244559834927069013108539)
            ·
              refine ⟨9366839752390603519662809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244559834927069013108539 9366839752390603519662809)
              ·
                refine ⟨7025129814292952639747107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366839752390603519662809 7025129814292952639747107)
                ·
                  refine ⟨10537694721439428959620661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025129814292952639747107 10537694721439428959620661)
                  ·
                    refine ⟨987908880134946464964437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10537694721439428959620661 987908880134946464964437)
                    ·
                      rfl

theorem cell23_5771837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_5771837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771837 prefixEnd_5771837 := by exact prefixLift 5771837
  have htrace : WordTrace (prefixWord ++ tailWord_5771837) baseStart_5771837 baseEnd_5771837 := by
    simpa [prefixWord, tailWord_5771837, baseEnd_5771837] using wordTrace_append hprefix tailTrace_5771837
  have hstable : (prefixWord ++ tailWord_5771837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771837).length < 2 ^ (prefixWord ++ tailWord_5771837).sum := by decide
  have hdescent : baseEnd_5771837 < baseStart_5771837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771840 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4]
def baseStart_5771840 : Nat := 118140960795 + 5771840 * 2 ^ 59
def prefixEnd_5771840 : Nat := 4983230072969 + 3 ^ 40 * 5771840 * 2
def baseEnd_5771840 : Nat := 2963728180846802883155797

theorem tailTrace_5771840 : CollatzResearch.WordTrace tailWord_5771840 prefixEnd_5771840 2963728180846802883155797 := by
  unfold tailWord_5771840
  simp only [CollatzResearch.WordTrace]
  refine ⟨105258149704808453318700487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140344199606411271091600649 105258149704808453318700487)
  ·
    refine ⟨157887224557212679978050731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105258149704808453318700487 157887224557212679978050731)
    ·
      refine ⟨236830836835819019967076097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157887224557212679978050731 236830836835819019967076097)
      ·
        refine ⟨177623127626864264975307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236830836835819019967076097 177623127626864264975307073)
        ·
          refine ⟨133217345720148198731480305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177623127626864264975307073 133217345720148198731480305)
          ·
            refine ⟨99913009290111149048610229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133217345720148198731480305 99913009290111149048610229)
            ·
              refine ⟨9366844620947920223307209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99913009290111149048610229 9366844620947920223307209)
              ·
                refine ⟨7025133465710940167480407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366844620947920223307209 7025133465710940167480407)
                ·
                  refine ⟨10537700198566410251220611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025133465710940167480407 10537700198566410251220611)
                  ·
                    refine ⟨15806550297849615376830917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10537700198566410251220611 15806550297849615376830917)
                    ·
                      refine ⟨2963728180846802883155797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15806550297849615376830917 2963728180846802883155797)
                      ·
                        rfl

theorem cell23_5771840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 4].length) (baseStart_5771840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771840 prefixEnd_5771840 := by exact prefixLift 5771840
  have htrace : WordTrace (prefixWord ++ tailWord_5771840) baseStart_5771840 baseEnd_5771840 := by
    simpa [prefixWord, tailWord_5771840, baseEnd_5771840] using wordTrace_append hprefix tailTrace_5771840
  have hstable : (prefixWord ++ tailWord_5771840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771840).length < 2 ^ (prefixWord ++ tailWord_5771840).sum := by decide
  have hdescent : baseEnd_5771840 < baseStart_5771840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771857 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_5771857 : Nat := 118140960795 + 5771857 * 2 ^ 59
def prefixEnd_5771857 : Nat := 4983230072969 + 3 ^ 40 * 5771857 * 2
def baseEnd_5771857 : Nat := 2963736910017929316643219

theorem tailTrace_5771857 : CollatzResearch.WordTrace tailWord_5771857 prefixEnd_5771857 2963736910017929316643219 := by
  unfold tailWord_5771857
  simp only [CollatzResearch.WordTrace]
  refine ⟨210516919450555318540769825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140344612967036879027179883 210516919450555318540769825)
  ·
    refine ⟨157887689587916488905577369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210516919450555318540769825 157887689587916488905577369)
    ·
      refine ⟨118415767190937366679183027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157887689587916488905577369 118415767190937366679183027)
      ·
        refine ⟨177623650786406050018774541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118415767190937366679183027 177623650786406050018774541)
        ·
          refine ⟨66608869044902268757040453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177623650786406050018774541 66608869044902268757040453)
          ·
            refine ⟨12489162945919175391945085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66608869044902268757040453 12489162945919175391945085)
            ·
              refine ⟨4683436104719690771979407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12489162945919175391945085 4683436104719690771979407)
              ·
                refine ⟨7025154157079536157969111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683436104719690771979407 7025154157079536157969111)
                ·
                  refine ⟨10537731235619304236953667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025154157079536157969111 10537731235619304236953667)
                  ·
                    refine ⟨15806596853428956355430501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10537731235619304236953667 15806596853428956355430501)
                    ·
                      refine ⟨2963736910017929316643219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15806596853428956355430501 2963736910017929316643219)
                      ·
                        rfl

theorem cell23_5771857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_5771857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771857 prefixEnd_5771857 := by exact prefixLift 5771857
  have htrace : WordTrace (prefixWord ++ tailWord_5771857) baseStart_5771857 baseEnd_5771857 := by
    simpa [prefixWord, tailWord_5771857, baseEnd_5771857] using wordTrace_append hprefix tailTrace_5771857
  have hstable : (prefixWord ++ tailWord_5771857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771857).length < 2 ^ (prefixWord ++ tailWord_5771857).sum := by decide
  have hdescent : baseEnd_5771857 < baseStart_5771857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771860 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_5771860 : Nat := 118140960795 + 5771860 * 2 ^ 59
def prefixEnd_5771860 : Nat := 4983230072969 + 3 ^ 40 * 5771860 * 2
def baseEnd_5771860 : Nat := 2963738450459892804905705

theorem tailTrace_5771860 : CollatzResearch.WordTrace tailWord_5771860 prefixEnd_5771860 2963738450459892804905705 := by
  unfold tailWord_5771860
  simp only [CollatzResearch.WordTrace]
  refine ⟨105258514434772225026564517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140344685913029633368752689 105258514434772225026564517)
  ·
    refine ⟨19735971456519792192480847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105258514434772225026564517 19735971456519792192480847)
    ·
      refine ⟨29603957184779688288721271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19735971456519792192480847 29603957184779688288721271)
      ·
        refine ⟨44405935777169532433081907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29603957184779688288721271 44405935777169532433081907)
        ·
          refine ⟨66608903665754298649622861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44405935777169532433081907 66608903665754298649622861)
          ·
            refine ⟨24978338874657861993608573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66608903665754298649622861 24978338874657861993608573)
            ·
              refine ⟨9366877077996698247603215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24978338874657861993608573 9366877077996698247603215)
              ·
                refine ⟨14050315616995047371404823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9366877077996698247603215 14050315616995047371404823)
                ·
                  refine ⟨21075473425492571057107235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14050315616995047371404823 21075473425492571057107235)
                  ·
                    refine ⟨31613210138238856585660853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21075473425492571057107235 31613210138238856585660853)
                    ·
                      refine ⟨2963738450459892804905705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31613210138238856585660853 2963738450459892804905705)
                      ·
                        rfl

theorem cell23_5771860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_5771860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771860 prefixEnd_5771860 := by exact prefixLift 5771860
  have htrace : WordTrace (prefixWord ++ tailWord_5771860) baseStart_5771860 baseEnd_5771860 := by
    simpa [prefixWord, tailWord_5771860, baseEnd_5771860] using wordTrace_append hprefix tailTrace_5771860
  have hstable : (prefixWord ++ tailWord_5771860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771860).length < 2 ^ (prefixWord ++ tailWord_5771860).sum := by decide
  have hdescent : baseEnd_5771860 < baseStart_5771860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771868 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_5771868 : Nat := 118140960795 + 5771868 * 2 ^ 59
def prefixEnd_5771868 : Nat := 4983230072969 + 3 ^ 40 * 5771868 * 2
def baseEnd_5771868 : Nat := 2963742558305128773605669

theorem tailTrace_5771868 : CollatzResearch.WordTrace tailWord_5771868 prefixEnd_5771868 2963742558305128773605669 := by
  unfold tailWord_5771868
  simp only [CollatzResearch.WordTrace]
  refine ⟨105258660326757733709710129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140344880435676978279613505 105258660326757733709710129)
  ·
    refine ⟨78943995245068300282282597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105258660326757733709710129 78943995245068300282282597)
    ·
      refine ⟨14801999108450306302927987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78943995245068300282282597 14801999108450306302927987)
      ·
        refine ⟨22202998662675459454391981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14801999108450306302927987 22202998662675459454391981)
        ·
          refine ⟨8326124498503297295396993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22202998662675459454391981 8326124498503297295396993)
          ·
            refine ⟨6244593373877472971547745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326124498503297295396993 6244593373877472971547745)
            ·
              refine ⟨4683445030408104728660809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244593373877472971547745 4683445030408104728660809)
              ·
                refine ⟨3512583772806078546495607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4683445030408104728660809 3512583772806078546495607)
                ·
                  refine ⟨5268875659209117819743411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512583772806078546495607 5268875659209117819743411)
                  ·
                    refine ⟨7903313488813676729615117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268875659209117819743411 7903313488813676729615117)
                    ·
                      refine ⟨2963742558305128773605669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903313488813676729615117 2963742558305128773605669)
                      ·
                        rfl

theorem cell23_5771868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_5771868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771868 prefixEnd_5771868 := by exact prefixLift 5771868
  have htrace : WordTrace (prefixWord ++ tailWord_5771868) baseStart_5771868 baseEnd_5771868 := by
    simpa [prefixWord, tailWord_5771868, baseEnd_5771868] using wordTrace_append hprefix tailTrace_5771868
  have hstable : (prefixWord ++ tailWord_5771868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771868).length < 2 ^ (prefixWord ++ tailWord_5771868).sum := by decide
  have hdescent : baseEnd_5771868 < baseStart_5771868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5771924 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_5771924 : Nat := 118140960795 + 5771924 * 2 ^ 59
def prefixEnd_5771924 : Nat := 4983230072969 + 3 ^ 40 * 5771924 * 2
def baseEnd_5771924 : Nat := 2963771313221780554505411

theorem tailTrace_5771924 : CollatzResearch.WordTrace tailWord_5771924 prefixEnd_5771924 2963771313221780554505411 := by
  unfold tailWord_5771924
  simp only [CollatzResearch.WordTrace]
  refine ⟨105259681570656294491729413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140346242094208392655639217 105259681570656294491729413)
  ·
    refine ⟨19736190294498055217199265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105259681570656294491729413 19736190294498055217199265)
    ·
      refine ⟨14802142720873541412899449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19736190294498055217199265 14802142720873541412899449)
      ·
        refine ⟨11101607040655156059674587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14802142720873541412899449 11101607040655156059674587)
        ·
          refine ⟨16652410560982734089511881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101607040655156059674587 16652410560982734089511881)
          ·
            refine ⟨12489307920737050567133911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16652410560982734089511881 12489307920737050567133911)
            ·
              refine ⟨18733961881105575850700867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489307920737050567133911 18733961881105575850700867)
              ·
                refine ⟨28100942821658363776051301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18733961881105575850700867 28100942821658363776051301)
                ·
                  refine ⟨5268926779060943208009619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28100942821658363776051301 5268926779060943208009619)
                  ·
                    refine ⟨7903390168591414812014429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5268926779060943208009619 7903390168591414812014429)
                    ·
                      refine ⟨2963771313221780554505411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903390168591414812014429 2963771313221780554505411)
                      ·
                        rfl

theorem cell23_5771924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_5771924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5771924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5771924 prefixEnd_5771924 := by exact prefixLift 5771924
  have htrace : WordTrace (prefixWord ++ tailWord_5771924) baseStart_5771924 baseEnd_5771924 := by
    simpa [prefixWord, tailWord_5771924, baseEnd_5771924] using wordTrace_append hprefix tailTrace_5771924
  have hstable : (prefixWord ++ tailWord_5771924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5771924).length < 2 ^ (prefixWord ++ tailWord_5771924).sum := by decide
  have hdescent : baseEnd_5771924 < baseStart_5771924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5771924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772087 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_5772087 : Nat := 118140960795 + 5772087 * 2 ^ 59
def prefixEnd_5772087 : Nat := 4983230072969 + 3 ^ 40 * 5772087 * 2
def baseEnd_5772087 : Nat := 2963855010568463416767161

theorem tailTrace_5772087 : CollatzResearch.WordTrace tailWord_5772087 prefixEnd_5772087 2963855010568463416767161 := by
  unfold tailWord_5772087
  simp only [CollatzResearch.WordTrace]
  refine ⟨210525308239722067821642515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140350205493148045214428343 210525308239722067821642515)
  ·
    refine ⟨315787962359583101732463773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210525308239722067821642515 315787962359583101732463773)
    ·
      refine ⟨118420485884843663149673915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315787962359583101732463773 118420485884843663149673915)
      ·
        refine ⟨177630728827265494724510873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118420485884843663149673915 177630728827265494724510873)
        ·
          refine ⟨133223046620449121043383155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177630728827265494724510873 133223046620449121043383155)
          ·
            refine ⟨199834569930673681565074733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133223046620449121043383155 199834569930673681565074733)
            ·
              refine ⟨74937963724002630586903025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199834569930673681565074733 74937963724002630586903025)
              ·
                refine ⟨56203472793001972940177269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74937963724002630586903025 56203472793001972940177269)
                ·
                  refine ⟨5269075574343934963141619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56203472793001972940177269 5269075574343934963141619)
                  ·
                    refine ⟨7903613361515902444712429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269075574343934963141619 7903613361515902444712429)
                    ·
                      refine ⟨2963855010568463416767161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903613361515902444712429 2963855010568463416767161)
                      ·
                        rfl

theorem cell23_5772087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_5772087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772087 prefixEnd_5772087 := by exact prefixLift 5772087
  have htrace : WordTrace (prefixWord ++ tailWord_5772087) baseStart_5772087 baseEnd_5772087 := by
    simpa [prefixWord, tailWord_5772087, baseEnd_5772087] using wordTrace_append hprefix tailTrace_5772087
  have hstable : (prefixWord ++ tailWord_5772087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772087).length < 2 ^ (prefixWord ++ tailWord_5772087).sum := by decide
  have hdescent : baseEnd_5772087 < baseStart_5772087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772104 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_5772104 : Nat := 118140960795 + 5772104 * 2 ^ 59
def prefixEnd_5772104 : Nat := 4983230072969 + 3 ^ 40 * 5772104 * 2
def baseEnd_5772104 : Nat := 2963863739739589850254583

theorem tailTrace_5772104 : CollatzResearch.WordTrace tailWord_5772104 prefixEnd_5772104 2963863739739589850254583 := by
  unfold tailWord_5772104
  simp only [CollatzResearch.WordTrace]
  refine ⟨105262964140330239862505683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140350618853773653150007577 105262964140330239862505683)
  ·
    refine ⟨157894446210495359793758525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105262964140330239862505683 157894446210495359793758525)
    ·
      refine ⟨59210417328935759922659447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157894446210495359793758525 59210417328935759922659447)
      ·
        refine ⟨88815625993403639883989171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59210417328935759922659447 88815625993403639883989171)
        ·
          refine ⟨133223438990105459825983757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88815625993403639883989171 133223438990105459825983757)
          ·
            refine ⟨49958789621289547434743909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133223438990105459825983757 49958789621289547434743909)
            ·
              refine ⟨9367273053991790144014483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49958789621289547434743909 9367273053991790144014483)
              ·
                refine ⟨14050909580987685216021725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367273053991790144014483 14050909580987685216021725)
                ·
                  refine ⟨5269091092870381956008147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14050909580987685216021725 5269091092870381956008147)
                  ·
                    refine ⟨7903636639305572934012221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269091092870381956008147 7903636639305572934012221)
                    ·
                      refine ⟨2963863739739589850254583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903636639305572934012221 2963863739739589850254583)
                      ·
                        rfl

theorem cell23_5772104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_5772104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772104 prefixEnd_5772104 := by exact prefixLift 5772104
  have htrace : WordTrace (prefixWord ++ tailWord_5772104) baseStart_5772104 baseEnd_5772104 := by
    simpa [prefixWord, tailWord_5772104, baseEnd_5772104] using wordTrace_append hprefix tailTrace_5772104
  have hstable : (prefixWord ++ tailWord_5772104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772104).length < 2 ^ (prefixWord ++ tailWord_5772104).sum := by decide
  have hdescent : baseEnd_5772104 < baseStart_5772104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772124 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_5772124 : Nat := 118140960795 + 5772124 * 2 ^ 59
def prefixEnd_5772124 : Nat := 4983230072969 + 3 ^ 40 * 5772124 * 2
def baseEnd_5772124 : Nat := 987958003117559924001497

theorem tailTrace_5772124 : CollatzResearch.WordTrace tailWord_5772124 prefixEnd_5772124 987958003117559924001497 := by
  unfold tailWord_5772124
  simp only [CollatzResearch.WordTrace]
  refine ⟨105263328870294011570369713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140351105160392015427159617 105263328870294011570369713)
  ·
    refine ⟨78947496652720508677777285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105263328870294011570369713 78947496652720508677777285)
    ·
      refine ⟨14802655622385095377083241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78947496652720508677777285 14802655622385095377083241)
      ·
        refine ⟨11101991716788821532812431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14802655622385095377083241 11101991716788821532812431)
        ·
          refine ⟨16652987575183232299218647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101991716788821532812431 16652987575183232299218647)
          ·
            refine ⟨24979481362774848448827971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16652987575183232299218647 24979481362774848448827971)
            ·
              refine ⟨37469222044162272673241957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24979481362774848448827971 37469222044162272673241957)
              ·
                refine ⟨7025479133280426126232867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37469222044162272673241957 7025479133280426126232867)
                ·
                  refine ⟨10538218699920639189349301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025479133280426126232867 10538218699920639189349301)
                  ·
                    refine ⟨987958003117559924001497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10538218699920639189349301 987958003117559924001497)
                    ·
                      rfl

theorem cell23_5772124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_5772124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772124 prefixEnd_5772124 := by exact prefixLift 5772124
  have htrace : WordTrace (prefixWord ++ tailWord_5772124) baseStart_5772124 baseEnd_5772124 := by
    simpa [prefixWord, tailWord_5772124, baseEnd_5772124] using wordTrace_append hprefix tailTrace_5772124
  have hstable : (prefixWord ++ tailWord_5772124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772124).length < 2 ^ (prefixWord ++ tailWord_5772124).sum := by decide
  have hdescent : baseEnd_5772124 < baseStart_5772124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772127 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 2, 6, 2]
def baseStart_5772127 : Nat := 118140960795 + 5772127 * 2 ^ 59
def prefixEnd_5772127 : Nat := 4983230072969 + 3 ^ 40 * 5772127 * 2
def baseEnd_5772127 : Nat := 2963875549794643260266977

theorem tailTrace_5772127 : CollatzResearch.WordTrace tailWord_5772127 prefixEnd_5772127 2963875549794643260266977 := by
  unfold tailWord_5772127
  simp only [CollatzResearch.WordTrace]
  refine ⟨210526767159577154653098635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140351178106384769768732423 210526767159577154653098635)
  ·
    refine ⟨315790150739365731979647953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210526767159577154653098635 315790150739365731979647953)
    ·
      refine ⟨236842613054524298984735965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315790150739365731979647953 236842613054524298984735965)
      ·
        refine ⟨88815979895446612119275987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236842613054524298984735965 88815979895446612119275987)
        ·
          refine ⟨133223969843169918178913981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88815979895446612119275987 133223969843169918178913981)
          ·
            refine ⟨49958988691188719317092743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133223969843169918178913981 49958988691188719317092743)
            ·
              refine ⟨74938483036783078975639115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49958988691188719317092743 74938483036783078975639115)
              ·
                refine ⟨112407724555174618463458673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74938483036783078975639115 112407724555174618463458673)
                ·
                  refine ⟨84305793416380963847594005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112407724555174618463458673 84305793416380963847594005)
                  ·
                    refine ⟨3951834066392857680355969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84305793416380963847594005 3951834066392857680355969)
                    ·
                      refine ⟨2963875549794643260266977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951834066392857680355969 2963875549794643260266977)
                      ·
                        rfl

theorem cell23_5772127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_5772127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772127 prefixEnd_5772127 := by exact prefixLift 5772127
  have htrace : WordTrace (prefixWord ++ tailWord_5772127) baseStart_5772127 baseEnd_5772127 := by
    simpa [prefixWord, tailWord_5772127, baseEnd_5772127] using wordTrace_append hprefix tailTrace_5772127
  have hstable : (prefixWord ++ tailWord_5772127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772127).length < 2 ^ (prefixWord ++ tailWord_5772127).sum := by decide
  have hdescent : baseEnd_5772127 < baseStart_5772127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772144 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2]
def baseStart_5772144 : Nat := 118140960795 + 5772144 * 2 ^ 59
def prefixEnd_5772144 : Nat := 4983230072969 + 3 ^ 40 * 5772144 * 2
def baseEnd_5772144 : Nat := 2963884278965769693754399

theorem tailTrace_5772144 : CollatzResearch.WordTrace tailWord_5772144 prefixEnd_5772144 2963884278965769693754399 := by
  unfold tailWord_5772144
  simp only [CollatzResearch.WordTrace]
  refine ⟨105263693600257783278233743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140351591467010377704311657 105263693600257783278233743)
  ·
    refine ⟨157895540400386674917350615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105263693600257783278233743 157895540400386674917350615)
    ·
      refine ⟨236843310600580012376025923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157895540400386674917350615 236843310600580012376025923)
      ·
        refine ⟨355264965900870018564038885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236843310600580012376025923 355264965900870018564038885)
        ·
          refine ⟨66612181106413128480757291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355264965900870018564038885 66612181106413128480757291)
          ·
            refine ⟨99918271659619692721135937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66612181106413128480757291 99918271659619692721135937)
            ·
              refine ⟨74938703744714769540851953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99918271659619692721135937 74938703744714769540851953)
              ·
                refine ⟨56204027808536077155638965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74938703744714769540851953 56204027808536077155638965)
                ·
                  refine ⟨5269127607050257233341153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56204027808536077155638965 5269127607050257233341153)
                  ·
                    refine ⟨3951845705287692925005865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269127607050257233341153 3951845705287692925005865)
                    ·
                      refine ⟨2963884278965769693754399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951845705287692925005865 2963884278965769693754399)
                      ·
                        rfl

theorem cell23_5772144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 5, 2, 2].length) (baseStart_5772144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772144 prefixEnd_5772144 := by exact prefixLift 5772144
  have htrace : WordTrace (prefixWord ++ tailWord_5772144) baseStart_5772144 baseEnd_5772144 := by
    simpa [prefixWord, tailWord_5772144, baseEnd_5772144] using wordTrace_append hprefix tailTrace_5772144
  have hstable : (prefixWord ++ tailWord_5772144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772144).length < 2 ^ (prefixWord ++ tailWord_5772144).sum := by decide
  have hdescent : baseEnd_5772144 < baseStart_5772144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772167 : List Nat := [1, 1, 4, 2, 3, 2, 2, 8]
def baseStart_5772167 : Nat := 118140960795 + 5772167 * 2 ^ 59
def prefixEnd_5772167 : Nat := 4983230072969 + 3 ^ 40 * 5772167 * 2
def baseEnd_5772167 : Nat := 109773929222993448287659

theorem tailTrace_5772167 : CollatzResearch.WordTrace tailWord_5772167 prefixEnd_5772167 109773929222993448287659 := by
  unfold tailWord_5772167
  simp only [CollatzResearch.WordTrace]
  refine ⟨210528226079432241484554755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140352150719621494323036503 210528226079432241484554755)
  ·
    refine ⟨315792339119148362226832133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210528226079432241484554755 315792339119148362226832133)
    ·
      refine ⟨59211063584840317917531025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315792339119148362226832133 59211063584840317917531025)
      ·
        refine ⟨44408297688630238438148269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59211063584840317917531025 44408297688630238438148269)
        ·
          refine ⟨16653111633236339414305601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44408297688630238438148269 16653111633236339414305601)
          ·
            refine ⟨12489833724927254560729201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16653111633236339414305601 12489833724927254560729201)
            ·
              refine ⟨9367375293695440920546901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489833724927254560729201 9367375293695440920546901)
              ·
                refine ⟨109773929222993448287659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9367375293695440920546901 109773929222993448287659)
                ·
                  rfl

theorem cell23_5772167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 8].length) (baseStart_5772167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772167 prefixEnd_5772167 := by exact prefixLift 5772167
  have htrace : WordTrace (prefixWord ++ tailWord_5772167) baseStart_5772167 baseEnd_5772167 := by
    simpa [prefixWord, tailWord_5772167, baseEnd_5772167] using wordTrace_append hprefix tailTrace_5772167
  have hstable : (prefixWord ++ tailWord_5772167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772167).length < 2 ^ (prefixWord ++ tailWord_5772167).sum := by decide
  have hdescent : baseEnd_5772167 < baseStart_5772167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772177 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_5772177 : Nat := 118140960795 + 5772177 * 2 ^ 59
def prefixEnd_5772177 : Nat := 4983230072969 + 3 ^ 40 * 5772177 * 2
def baseEnd_5772177 : Nat := 2963901223827368064641747

theorem tailTrace_5772177 : CollatzResearch.WordTrace tailWord_5772177 prefixEnd_5772177 2963901223827368064641747 := by
  unfold tailWord_5772177
  simp only [CollatzResearch.WordTrace]
  refine ⟨210528590809396013192418785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140352393872930675461612523 210528590809396013192418785)
  ·
    refine ⟨157896443107047009894314089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210528590809396013192418785 157896443107047009894314089)
    ·
      refine ⟨118422332330285257420735567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157896443107047009894314089 118422332330285257420735567)
      ·
        refine ⟨177633498495427886131103351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118422332330285257420735567 177633498495427886131103351)
        ·
          refine ⟨266450247743141829196655027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177633498495427886131103351 266450247743141829196655027)
          ·
            refine ⟨399675371614712743794982541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266450247743141829196655027 399675371614712743794982541)
            ·
              refine ⟨149878264355517278923118453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399675371614712743794982541 149878264355517278923118453)
              ·
                refine ⟨14051087283329744899042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149878264355517278923118453 14051087283329744899042355)
                ·
                  refine ⟨21076630924994617348563533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051087283329744899042355 21076630924994617348563533)
                  ·
                    refine ⟨7903736596872981505711325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21076630924994617348563533 7903736596872981505711325)
                    ·
                      refine ⟨2963901223827368064641747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903736596872981505711325 2963901223827368064641747)
                      ·
                        rfl

theorem cell23_5772177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_5772177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772177 prefixEnd_5772177 := by exact prefixLift 5772177
  have htrace : WordTrace (prefixWord ++ tailWord_5772177) baseStart_5772177 baseEnd_5772177 := by
    simpa [prefixWord, tailWord_5772177, baseEnd_5772177] using wordTrace_append hprefix tailTrace_5772177
  have hstable : (prefixWord ++ tailWord_5772177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772177).length < 2 ^ (prefixWord ++ tailWord_5772177).sum := by decide
  have hdescent : baseEnd_5772177 < baseStart_5772177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772178 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5772178 : Nat := 118140960795 + 5772178 * 2 ^ 59
def prefixEnd_5772178 : Nat := 4983230072969 + 3 ^ 40 * 5772178 * 2
def baseEnd_5772178 : Nat := 2963901737308022560729243

theorem tailTrace_5772178 : CollatzResearch.WordTrace tailWord_5772178 prefixEnd_5772178 2963901737308022560729243 := by
  unfold tailWord_5772178
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632156820598097590801297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140352418188261593575470125 52632156820598097590801297)
  ·
    refine ⟨39474117615448573193100973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52632156820598097590801297 39474117615448573193100973)
    ·
      refine ⟨14802794105793214947412865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39474117615448573193100973 14802794105793214947412865)
      ·
        refine ⟨11102095579344911210559649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14802794105793214947412865 11102095579344911210559649)
        ·
          refine ⟨8326571684508683407919737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11102095579344911210559649 8326571684508683407919737)
          ·
            refine ⟨6244928763381512555939803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326571684508683407919737 6244928763381512555939803)
            ·
              refine ⟨9367393145072268833909705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244928763381512555939803 9367393145072268833909705)
              ·
                refine ⟨7025544858804201625432279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367393145072268833909705 7025544858804201625432279)
                ·
                  refine ⟨10538317288206302438148419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025544858804201625432279 10538317288206302438148419)
                  ·
                    refine ⟨15807475932309453657222629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10538317288206302438148419 15807475932309453657222629)
                    ·
                      refine ⟨2963901737308022560729243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15807475932309453657222629 2963901737308022560729243)
                      ·
                        rfl

theorem cell23_5772178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5772178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772178 prefixEnd_5772178 := by exact prefixLift 5772178
  have htrace : WordTrace (prefixWord ++ tailWord_5772178) baseStart_5772178 baseEnd_5772178 := by
    simpa [prefixWord, tailWord_5772178, baseEnd_5772178] using wordTrace_append hprefix tailTrace_5772178
  have hstable : (prefixWord ++ tailWord_5772178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772178).length < 2 ^ (prefixWord ++ tailWord_5772178).sum := by decide
  have hdescent : baseEnd_5772178 < baseStart_5772178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772181 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_5772181 : Nat := 118140960795 + 5772181 * 2 ^ 59
def prefixEnd_5772181 : Nat := 4983230072969 + 3 ^ 40 * 5772181 * 2
def baseEnd_5772181 : Nat := 2963903277749986048991729

theorem tailTrace_5772181 : CollatzResearch.WordTrace tailWord_5772181 prefixEnd_5772181 2963903277749986048991729 := by
  unfold tailWord_5772181
  simp only [CollatzResearch.WordTrace]
  refine ⟨210528736701381521875564397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140352491134254347917042931 210528736701381521875564397)
  ·
    refine ⟨78948276263018070703336649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210528736701381521875564397 78948276263018070703336649)
    ·
      refine ⟨59211207197263553027502487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78948276263018070703336649 59211207197263553027502487)
      ·
        refine ⟨88816810795895329541253731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59211207197263553027502487 88816810795895329541253731)
        ·
          refine ⟨133225216193842994311880597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88816810795895329541253731 133225216193842994311880597)
          ·
            refine ⟨6244932009086390358369403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133225216193842994311880597 6244932009086390358369403)
            ·
              refine ⟨9367398013629585537554105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244932009086390358369403 9367398013629585537554105)
              ·
                refine ⟨7025548510222189153165579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367398013629585537554105 7025548510222189153165579)
                ·
                  refine ⟨10538322765333283729748369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025548510222189153165579 10538322765333283729748369)
                  ·
                    refine ⟨7903742073999962797311277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10538322765333283729748369 7903742073999962797311277)
                    ·
                      refine ⟨2963903277749986048991729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903742073999962797311277 2963903277749986048991729)
                      ·
                        rfl

theorem cell23_5772181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_5772181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772181 prefixEnd_5772181 := by exact prefixLift 5772181
  have htrace : WordTrace (prefixWord ++ tailWord_5772181) baseStart_5772181 baseEnd_5772181 := by
    simpa [prefixWord, tailWord_5772181, baseEnd_5772181] using wordTrace_append hprefix tailTrace_5772181
  have hstable : (prefixWord ++ tailWord_5772181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772181).length < 2 ^ (prefixWord ++ tailWord_5772181).sum := by decide
  have hdescent : baseEnd_5772181 < baseStart_5772181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772194 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5772194 : Nat := 118140960795 + 5772194 * 2 ^ 59
def prefixEnd_5772194 : Nat := 4983230072969 + 3 ^ 40 * 5772194 * 2
def baseEnd_5772194 : Nat := 2963909952998494498129169

theorem tailTrace_5772194 : CollatzResearch.WordTrace tailWord_5772194 prefixEnd_5772194 2963909952998494498129169 := by
  unfold tailWord_5772194
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632302712583606273946909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140352807233556283397191757 52632302712583606273946909)
  ·
    refine ⟨19737113517218852352730091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52632302712583606273946909 19737113517218852352730091)
    ·
      refine ⟨29605670275828278529095137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19737113517218852352730091 29605670275828278529095137)
      ·
        refine ⟨22204252706871208896821353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29605670275828278529095137 22204252706871208896821353)
        ·
          refine ⟨16653189530153406672616015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22204252706871208896821353 16653189530153406672616015)
          ·
            refine ⟨24979784295230110008924023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16653189530153406672616015 24979784295230110008924023)
            ·
              refine ⟨37469676442845165013386035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24979784295230110008924023 37469676442845165013386035)
              ·
                refine ⟨56204514664267747520079053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37469676442845165013386035 56204514664267747520079053)
                ·
                  refine ⟨21076692999100405320029645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56204514664267747520079053 21076692999100405320029645)
                  ·
                    refine ⟨7903759874662651995011117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21076692999100405320029645 7903759874662651995011117)
                    ·
                      refine ⟨2963909952998494498129169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903759874662651995011117 2963909952998494498129169)
                      ·
                        rfl

theorem cell23_5772194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5772194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772194 prefixEnd_5772194 := by exact prefixLift 5772194
  have htrace : WordTrace (prefixWord ++ tailWord_5772194) baseStart_5772194 baseEnd_5772194 := by
    simpa [prefixWord, tailWord_5772194, baseEnd_5772194] using wordTrace_append hprefix tailTrace_5772194
  have hstable : (prefixWord ++ tailWord_5772194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772194).length < 2 ^ (prefixWord ++ tailWord_5772194).sum := by decide
  have hdescent : baseEnd_5772194 < baseStart_5772194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772212 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_5772212 : Nat := 118140960795 + 5772212 * 2 ^ 59
def prefixEnd_5772212 : Nat := 4983230072969 + 3 ^ 40 * 5772212 * 2
def baseEnd_5772212 : Nat := 2963919195650275427704087

theorem tailTrace_5772212 : CollatzResearch.WordTrace tailWord_5772212 prefixEnd_5772212 2963919195650275427704087 := by
  unfold tailWord_5772212
  simp only [CollatzResearch.WordTrace]
  refine ⟨105264933682134607084971445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140353244909512809446628593 105264933682134607084971445)
  ·
    refine ⟨9868587532700119414216073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105264933682134607084971445 9868587532700119414216073)
    ·
      refine ⟨7401440649525089560662055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9868587532700119414216073 7401440649525089560662055)
      ·
        refine ⟨11102160974287634340993083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401440649525089560662055 11102160974287634340993083)
        ·
          refine ⟨16653241461431451511489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11102160974287634340993083 16653241461431451511489625)
          ·
            refine ⟨12489931096073588633617219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16653241461431451511489625 12489931096073588633617219)
            ·
              refine ⟨18734896644110382950425829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489931096073588633617219 18734896644110382950425829)
              ·
                refine ⟨3512793120770696803204843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18734896644110382950425829 3512793120770696803204843)
                ·
                  refine ⟨5269189681156045204807265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512793120770696803204843 5269189681156045204807265)
                  ·
                    refine ⟨3951892260867033903605449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269189681156045204807265 3951892260867033903605449)
                    ·
                      refine ⟨2963919195650275427704087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951892260867033903605449 2963919195650275427704087)
                      ·
                        rfl

theorem cell23_5772212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_5772212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772212 prefixEnd_5772212 := by exact prefixLift 5772212
  have htrace : WordTrace (prefixWord ++ tailWord_5772212) baseStart_5772212 baseEnd_5772212 := by
    simpa [prefixWord, tailWord_5772212, baseEnd_5772212] using wordTrace_append hprefix tailTrace_5772212
  have hstable : (prefixWord ++ tailWord_5772212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772212).length < 2 ^ (prefixWord ++ tailWord_5772212).sum := by decide
  have hdescent : baseEnd_5772212 < baseStart_5772212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772217 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5772217 : Nat := 118140960795 + 5772217 * 2 ^ 59
def prefixEnd_5772217 : Nat := 4983230072969 + 3 ^ 40 * 5772217 * 2
def baseEnd_5772217 : Nat := 2963921763053547908141563

theorem tailTrace_5772217 : CollatzResearch.WordTrace tailWord_5772217 prefixEnd_5772217 2963921763053547908141563 := by
  unfold tailWord_5772217
  simp only [CollatzResearch.WordTrace]
  refine ⟨210530049729251100023874905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140353366486167400015916603 210530049729251100023874905)
  ·
    refine ⟨157897537296938325017906179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210530049729251100023874905 157897537296938325017906179)
    ·
      refine ⟨236846305945407487526859269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157897537296938325017906179 236846305945407487526859269)
      ·
        refine ⟨44408682364763903911286113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236846305945407487526859269 44408682364763903911286113)
        ·
          refine ⟨33306511773572927933464585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44408682364763903911286113 33306511773572927933464585)
          ·
            refine ⟨24979883830179695950098439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33306511773572927933464585 24979883830179695950098439)
            ·
              refine ⟨37469825745269543925147659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24979883830179695950098439 37469825745269543925147659)
              ·
                refine ⟨56204738617904315887721489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37469825745269543925147659 56204738617904315887721489)
                ·
                  refine ⟨42153553963428236915791117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56204738617904315887721489 42153553963428236915791117)
                  ·
                    refine ⟨15807582736285588843421669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42153553963428236915791117 15807582736285588843421669)
                    ·
                      refine ⟨2963921763053547908141563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15807582736285588843421669 2963921763053547908141563)
                      ·
                        rfl

theorem cell23_5772217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5772217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772217 prefixEnd_5772217 := by exact prefixLift 5772217
  have htrace : WordTrace (prefixWord ++ tailWord_5772217) baseStart_5772217 baseEnd_5772217 := by
    simpa [prefixWord, tailWord_5772217, baseEnd_5772217] using wordTrace_append hprefix tailTrace_5772217
  have hstable : (prefixWord ++ tailWord_5772217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772217).length < 2 ^ (prefixWord ++ tailWord_5772217).sum := by decide
  have hdescent : baseEnd_5772217 < baseStart_5772217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772228 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_5772228 : Nat := 118140960795 + 5772228 * 2 ^ 59
def prefixEnd_5772228 : Nat := 4983230072969 + 3 ^ 40 * 5772228 * 2
def baseEnd_5772228 : Nat := 2963927411340747365104013

theorem tailTrace_5772228 : CollatzResearch.WordTrace tailWord_5772228 prefixEnd_5772228 2963927411340747365104013 := by
  unfold tailWord_5772228
  simp only [CollatzResearch.WordTrace]
  refine ⟨105265225466105624451262669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140353633954807499268350225 105265225466105624451262669)
  ·
    refine ⟨39474459549789609169223501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105265225466105624451262669 39474459549789609169223501)
    ·
      refine ⟨14802922331171103438458813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39474459549789609169223501 14802922331171103438458813)
      ·
        refine ⟨5551095874189163789422055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14802922331171103438458813 5551095874189163789422055)
        ·
          refine ⟨8326643811283745684133083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551095874189163789422055 8326643811283745684133083)
          ·
            refine ⟨12489965716925618526199625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326643811283745684133083 12489965716925618526199625)
            ·
              refine ⟨9367474287694213894649719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489965716925618526199625 9367474287694213894649719)
              ·
                refine ⟨14051211431541320841974579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367474287694213894649719 14051211431541320841974579)
                ·
                  refine ⟨21076817147311981262961869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051211431541320841974579 21076817147311981262961869)
                  ·
                    refine ⟨7903806430241992973610701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21076817147311981262961869 7903806430241992973610701)
                    ·
                      refine ⟨2963927411340747365104013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903806430241992973610701 2963927411340747365104013)
                      ·
                        rfl

theorem cell23_5772228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_5772228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772228 prefixEnd_5772228 := by exact prefixLift 5772228
  have htrace : WordTrace (prefixWord ++ tailWord_5772228) baseStart_5772228 baseEnd_5772228 := by
    simpa [prefixWord, tailWord_5772228, baseEnd_5772228] using wordTrace_append hprefix tailTrace_5772228
  have hstable : (prefixWord ++ tailWord_5772228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772228).length < 2 ^ (prefixWord ++ tailWord_5772228).sum := by decide
  have hdescent : baseEnd_5772228 < baseStart_5772228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772255 : List Nat := [1, 1, 2, 3, 5, 2, 2, 1, 1, 3, 2]
def baseStart_5772255 : Nat := 118140960795 + 5772255 * 2 ^ 59
def prefixEnd_5772255 : Nat := 4983230072969 + 3 ^ 40 * 5772255 * 2
def baseEnd_5772255 : Nat := 2963941275318418759466389

theorem tailTrace_5772255 : CollatzResearch.WordTrace tailWord_5772255 prefixEnd_5772255 2963941275318418759466389 := by
  unfold tailWord_5772255
  simp only [CollatzResearch.WordTrace]
  refine ⟨210531435703113432513758219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140354290468742288342505479 210531435703113432513758219)
  ·
    refine ⟨315797153554670148770637329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210531435703113432513758219 315797153554670148770637329)
    ·
      refine ⟨236847865166002611577977997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315797153554670148770637329 236847865166002611577977997)
      ·
        refine ⟨88817949437250979341741749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236847865166002611577977997 88817949437250979341741749)
        ·
          refine ⟨8326682759742279313288289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88817949437250979341741749 8326682759742279313288289)
          ·
            refine ⟨6245012069806709484966217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8326682759742279313288289 6245012069806709484966217)
            ·
              refine ⟨4683759052355032113724663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6245012069806709484966217 4683759052355032113724663)
              ·
                refine ⟨7025638578532548170586995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683759052355032113724663 7025638578532548170586995)
                ·
                  refine ⟨10538457867798822255880493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025638578532548170586995 10538457867798822255880493)
                  ·
                    refine ⟨3951921700424558345955185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10538457867798822255880493 3951921700424558345955185)
                    ·
                      refine ⟨2963941275318418759466389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3951921700424558345955185 2963941275318418759466389)
                      ·
                        rfl

theorem cell23_5772255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_5772255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772255 prefixEnd_5772255 := by exact prefixLift 5772255
  have htrace : WordTrace (prefixWord ++ tailWord_5772255) baseStart_5772255 baseEnd_5772255 := by
    simpa [prefixWord, tailWord_5772255, baseEnd_5772255] using wordTrace_append hprefix tailTrace_5772255
  have hstable : (prefixWord ++ tailWord_5772255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772255).length < 2 ^ (prefixWord ++ tailWord_5772255).sum := by decide
  have hdescent : baseEnd_5772255 < baseStart_5772255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772284 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_5772284 : Nat := 118140960795 + 5772284 * 2 ^ 59
def prefixEnd_5772284 : Nat := 4983230072969 + 3 ^ 40 * 5772284 * 2
def baseEnd_5772284 : Nat := 2963956166257399146003755

theorem tailTrace_5772284 : CollatzResearch.WordTrace tailWord_5772284 prefixEnd_5772284 2963956166257399146003755 := by
  unfold tailWord_5772284
  simp only [CollatzResearch.WordTrace]
  refine ⟨105266246710004185233281953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140354995613338913644375937 105266246710004185233281953)
  ·
    refine ⟨78949685032503138924961465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105266246710004185233281953 78949685032503138924961465)
    ·
      refine ⟨59212263774377354193721099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78949685032503138924961465 59212263774377354193721099)
      ·
        refine ⟨88818395661566031290581649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59212263774377354193721099 88818395661566031290581649)
        ·
          refine ⟨66613796746174523467936237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88818395661566031290581649 66613796746174523467936237)
          ·
            refine ⟨24980173779815446300476089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66613796746174523467936237 24980173779815446300476089)
            ·
              refine ⟨18735130334861584725357067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24980173779815446300476089 18735130334861584725357067)
              ·
                refine ⟨28102695502292377088035601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18735130334861584725357067 28102695502292377088035601)
                ·
                  refine ⟨21077021626719282816026701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28102695502292377088035601 21077021626719282816026701)
                  ·
                    refine ⟨7903883110019731056010013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21077021626719282816026701 7903883110019731056010013)
                    ·
                      refine ⟨2963956166257399146003755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7903883110019731056010013 2963956166257399146003755)
                      ·
                        rfl

theorem cell23_5772284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_5772284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772284 prefixEnd_5772284 := by exact prefixLift 5772284
  have htrace : WordTrace (prefixWord ++ tailWord_5772284) baseStart_5772284 baseEnd_5772284 := by
    simpa [prefixWord, tailWord_5772284, baseEnd_5772284] using wordTrace_append hprefix tailTrace_5772284
  have hstable : (prefixWord ++ tailWord_5772284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772284).length < 2 ^ (prefixWord ++ tailWord_5772284).sum := by decide
  have hdescent : baseEnd_5772284 < baseStart_5772284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772358 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5772358 : Nat := 118140960795 + 5772358 * 2 ^ 59
def prefixEnd_5772358 : Nat := 4983230072969 + 3 ^ 40 * 5772358 * 2
def baseEnd_5772358 : Nat := 2963994163825831856478415

theorem tailTrace_5772358 : CollatzResearch.WordTrace tailWord_5772358 prefixEnd_5772358 2963994163825831856478415 := by
  unfold tailWord_5772358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6579224763179383784523679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140356794947826854069838485 6579224763179383784523679)
  ·
    refine ⟨9868837144769075676785519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6579224763179383784523679 9868837144769075676785519)
    ·
      refine ⟨14803255717153613515178279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9868837144769075676785519 14803255717153613515178279)
      ·
        refine ⟨22204883575730420272767419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14803255717153613515178279 22204883575730420272767419)
        ·
          refine ⟨33307325363595630409151129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22204883575730420272767419 33307325363595630409151129)
          ·
            refine ⟨24980494022696722806863347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33307325363595630409151129 24980494022696722806863347)
            ·
              refine ⟨37470741034045084210295021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24980494022696722806863347 37470741034045084210295021)
              ·
                refine ⟨14051527887766906578860633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37470741034045084210295021 14051527887766906578860633)
                ·
                  refine ⟨10538645915825179934145475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14051527887766906578860633 10538645915825179934145475)
                  ·
                    refine ⟨15807968873737769901218213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10538645915825179934145475 15807968873737769901218213)
                    ·
                      refine ⟨2963994163825831856478415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15807968873737769901218213 2963994163825831856478415)
                      ·
                        rfl

theorem cell23_5772358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5772358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772358 prefixEnd_5772358 := by exact prefixLift 5772358
  have htrace : WordTrace (prefixWord ++ tailWord_5772358) baseStart_5772358 baseEnd_5772358 := by
    simpa [prefixWord, tailWord_5772358, baseEnd_5772358] using wordTrace_append hprefix tailTrace_5772358
  have hstable : (prefixWord ++ tailWord_5772358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772358).length < 2 ^ (prefixWord ++ tailWord_5772358).sum := by decide
  have hdescent : baseEnd_5772358 < baseStart_5772358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772425 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 1, 1, 3]
def baseStart_5772425 : Nat := 118140960795 + 5772425 * 2 ^ 59
def prefixEnd_5772425 : Nat := 4983230072969 + 3 ^ 40 * 5772425 * 2
def baseEnd_5772425 : Nat := 2964028567029683094340607

theorem tailTrace_5772425 : CollatzResearch.WordTrace tailWord_5772425 prefixEnd_5772425 2964028567029683094340607 := by
  unfold tailWord_5772425
  simp only [CollatzResearch.WordTrace]
  refine ⟨210537636112497551547446729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140358424074998367698297819 210537636112497551547446729)
  ·
    refine ⟨157903227084373163660585047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210537636112497551547446729 157903227084373163660585047)
    ·
      refine ⟨236854840626559745490877571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157903227084373163660585047 236854840626559745490877571)
      ·
        refine ⟨355282260939839618236316357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236854840626559745490877571 355282260939839618236316357)
        ·
          refine ⟨66615423926219928419309317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355282260939839618236316357 66615423926219928419309317)
          ·
            refine ⟨12490391986166236578620497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66615423926219928419309317 12490391986166236578620497)
            ·
              refine ⟨9367793989624677433965373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12490391986166236578620497 9367793989624677433965373)
              ·
                refine ⟨3512922746109254037737015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9367793989624677433965373 3512922746109254037737015)
                ·
                  refine ⟨5269384119163881056605523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512922746109254037737015 5269384119163881056605523)
                  ·
                    refine ⟨7904076178745821584908285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269384119163881056605523 7904076178745821584908285)
                    ·
                      refine ⟨2964028567029683094340607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7904076178745821584908285 2964028567029683094340607)
                      ·
                        rfl

theorem cell23_5772425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 1, 3].length) (baseStart_5772425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772425 prefixEnd_5772425 := by exact prefixLift 5772425
  have htrace : WordTrace (prefixWord ++ tailWord_5772425) baseStart_5772425 baseEnd_5772425 := by
    simpa [prefixWord, tailWord_5772425, baseEnd_5772425] using wordTrace_append hprefix tailTrace_5772425
  have hstable : (prefixWord ++ tailWord_5772425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772425).length < 2 ^ (prefixWord ++ tailWord_5772425).sum := by decide
  have hdescent : baseEnd_5772425 < baseStart_5772425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772458 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5772458 : Nat := 118140960795 + 5772458 * 2 ^ 59
def prefixEnd_5772458 : Nat := 4983230072969 + 3 ^ 40 * 5772458 * 2
def baseEnd_5772458 : Nat := 988015170630427155075985

theorem tailTrace_5772458 : CollatzResearch.WordTrace tailWord_5772458 prefixEnd_5772458 988015170630427155075985 := by
  unfold tailWord_5772458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52634709930344499545849507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140359226480918665455598685 52634709930344499545849507)
  ·
    refine ⟨78952064895516749318774261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52634709930344499545849507 78952064895516749318774261)
    ·
      refine ⟨7401756083954695248635087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78952064895516749318774261 7401756083954695248635087)
      ·
        refine ⟨11102634125932042872952631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401756083954695248635087 11102634125932042872952631)
        ·
          refine ⟨16653951188898064309428947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11102634125932042872952631 16653951188898064309428947)
          ·
            refine ⟨24980926783347096464143421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16653951188898064309428947 24980926783347096464143421)
            ·
              refine ⟨9367847543755161174053783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24980926783347096464143421 9367847543755161174053783)
              ·
                refine ⟨14051771315632741761080675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367847543755161174053783 14051771315632741761080675)
                ·
                  refine ⟨21077656973449112641621013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051771315632741761080675 21077656973449112641621013)
                  ·
                    refine ⟨988015170630427155075985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21077656973449112641621013 988015170630427155075985)
                    ·
                      rfl

theorem cell23_5772458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5772458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772458 prefixEnd_5772458 := by exact prefixLift 5772458
  have htrace : WordTrace (prefixWord ++ tailWord_5772458) baseStart_5772458 baseEnd_5772458 := by
    simpa [prefixWord, tailWord_5772458, baseEnd_5772458] using wordTrace_append hprefix tailTrace_5772458
  have hstable : (prefixWord ++ tailWord_5772458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772458).length < 2 ^ (prefixWord ++ tailWord_5772458).sum := by decide
  have hdescent : baseEnd_5772458 < baseStart_5772458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772465 : List Nat := [1, 2, 2, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5772465 : Nat := 118140960795 + 5772465 * 2 ^ 59
def prefixEnd_5772465 : Nat := 4983230072969 + 3 ^ 40 * 5772465 * 2
def baseEnd_5772465 : Nat := 2964049106255862937840423

theorem tailTrace_5772465 : CollatzResearch.WordTrace tailWord_5772465 prefixEnd_5772465 2964049106255862937840423 := by
  unfold tailWord_5772465
  simp only [CollatzResearch.WordTrace]
  refine ⟨210539095032352638378902849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140359396688235092252601899 210539095032352638378902849)
  ·
    refine ⟨157904321274264478784177137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210539095032352638378902849 157904321274264478784177137)
    ·
      refine ⟨118428240955698359088132853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157904321274264478784177137 118428240955698359088132853)
      ·
        refine ⟨11102647589596721164512455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118428240955698359088132853 11102647589596721164512455)
        ·
          refine ⟨16653971384395081746768683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11102647589596721164512455 16653971384395081746768683)
          ·
            refine ⟨24980957076592622620153025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16653971384395081746768683 24980957076592622620153025)
            ·
              refine ⟨18735717807444466965114769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24980957076592622620153025 18735717807444466965114769)
              ·
                refine ⟨14051788355583350223836077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18735717807444466965114769 14051788355583350223836077)
                ·
                  refine ⟨5269420633343756333938529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14051788355583350223836077 5269420633343756333938529)
                  ·
                    refine ⟨3952065475007817250453897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269420633343756333938529 3952065475007817250453897)
                    ·
                      refine ⟨2964049106255862937840423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952065475007817250453897 2964049106255862937840423)
                      ·
                        rfl

theorem cell23_5772465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5772465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772465 prefixEnd_5772465 := by exact prefixLift 5772465
  have htrace : WordTrace (prefixWord ++ tailWord_5772465) baseStart_5772465 baseEnd_5772465 := by
    simpa [prefixWord, tailWord_5772465, baseEnd_5772465] using wordTrace_append hprefix tailTrace_5772465
  have hstable : (prefixWord ++ tailWord_5772465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772465).length < 2 ^ (prefixWord ++ tailWord_5772465).sum := by decide
  have hdescent : baseEnd_5772465 < baseStart_5772465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772498 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5772498 : Nat := 118140960795 + 5772498 * 2 ^ 59
def prefixEnd_5772498 : Nat := 4983230072969 + 3 ^ 40 * 5772498 * 2
def baseEnd_5772498 : Nat := 2964066051117461308727771

theorem tailTrace_5772498 : CollatzResearch.WordTrace tailWord_5772498 prefixEnd_5772498 2964066051117461308727771 := by
  unfold tailWord_5772498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635074660308271253713537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140360199094155390009902765 52635074660308271253713537)
  ·
    refine ⟨39476305995231203440285153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52635074660308271253713537 39476305995231203440285153)
    ·
      refine ⟨29607229496423402580213865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39476305995231203440285153 29607229496423402580213865)
      ·
        refine ⟨22205422122317551935160399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29607229496423402580213865 22205422122317551935160399)
        ·
          refine ⟨33308133183476327902740599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22205422122317551935160399 33308133183476327902740599)
          ·
            refine ⟨49962199775214491854110899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33308133183476327902740599 49962199775214491854110899)
            ·
              refine ⟨74943299662821737781166349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49962199775214491854110899 74943299662821737781166349)
              ·
                refine ⟨28103737373558151667937381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74943299662821737781166349 28103737373558151667937381)
                ·
                  refine ⟨5269450757542153437738259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28103737373558151667937381 5269450757542153437738259)
                  ·
                    refine ⟨7904176136313230156607389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269450757542153437738259 7904176136313230156607389)
                    ·
                      refine ⟨2964066051117461308727771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7904176136313230156607389 2964066051117461308727771)
                      ·
                        rfl

theorem cell23_5772498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5772498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772498 prefixEnd_5772498 := by exact prefixLift 5772498
  have htrace : WordTrace (prefixWord ++ tailWord_5772498) baseStart_5772498 baseEnd_5772498 := by
    simpa [prefixWord, tailWord_5772498, baseEnd_5772498] using wordTrace_append hprefix tailTrace_5772498
  have hstable : (prefixWord ++ tailWord_5772498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772498).length < 2 ^ (prefixWord ++ tailWord_5772498).sum := by decide
  have hdescent : baseEnd_5772498 < baseStart_5772498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772509 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5772509 : Nat := 118140960795 + 5772509 * 2 ^ 59
def prefixEnd_5772509 : Nat := 4983230072969 + 3 ^ 40 * 5772509 * 2
def baseEnd_5772509 : Nat := 988023899801553588563407

theorem tailTrace_5772509 : CollatzResearch.WordTrace tailWord_5772509 prefixEnd_5772509 988023899801553588563407 := by
  unfold tailWord_5772509
  simp only [CollatzResearch.WordTrace]
  refine ⟨210540699844193233893504581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140360466562795489262336387 210540699844193233893504581)
  ·
    refine ⟨39476381220786231355032109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210540699844193233893504581 39476381220786231355032109)
    ·
      refine ⟨14803642957794836758137041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39476381220786231355032109 14803642957794836758137041)
      ·
        refine ⟨11102732218346127568602781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14803642957794836758137041 11102732218346127568602781)
        ·
          refine ⟨4163524581879797838226043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11102732218346127568602781 4163524581879797838226043)
          ·
            refine ⟨6245286872819696757339065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163524581879797838226043 6245286872819696757339065)
            ·
              refine ⟨4683965154614772568004299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6245286872819696757339065 4683965154614772568004299)
              ·
                refine ⟨7025947731922158852006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683965154614772568004299 7025947731922158852006449)
                ·
                  refine ⟨5269460798941619139004837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7025947731922158852006449 5269460798941619139004837)
                  ·
                    refine ⟨988023899801553588563407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5269460798941619139004837 988023899801553588563407)
                    ·
                      rfl

theorem cell23_5772509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5772509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772509 prefixEnd_5772509 := by exact prefixLift 5772509
  have htrace : WordTrace (prefixWord ++ tailWord_5772509) baseStart_5772509 baseEnd_5772509 := by
    simpa [prefixWord, tailWord_5772509, baseEnd_5772509] using wordTrace_append hprefix tailTrace_5772509
  have hstable : (prefixWord ++ tailWord_5772509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772509).length < 2 ^ (prefixWord ++ tailWord_5772509).sum := by decide
  have hdescent : baseEnd_5772509 < baseStart_5772509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772525 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5772525 : Nat := 118140960795 + 5772525 * 2 ^ 59
def prefixEnd_5772525 : Nat := 4983230072969 + 3 ^ 40 * 5772525 * 2
def baseEnd_5772525 : Nat := 2964079915095132703090147

theorem tailTrace_5772525 : CollatzResearch.WordTrace tailWord_5772525 prefixEnd_5772525 2964079915095132703090147 := by
  unfold tailWord_5772525
  simp only [CollatzResearch.WordTrace]
  refine ⟨210541283412135268626087029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140360855608090179084058019 210541283412135268626087029)
  ·
    refine ⟨19738245319887681433695659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210541283412135268626087029 19738245319887681433695659)
    ·
      refine ⟨29607367979831522150543489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19738245319887681433695659 29607367979831522150543489)
      ·
        refine ⟨22205525984873641612907617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29607367979831522150543489 22205525984873641612907617)
        ·
          refine ⟨16654144488655231209680713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22205525984873641612907617 16654144488655231209680713)
          ·
            refine ⟨12490608366491423407260535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16654144488655231209680713 12490608366491423407260535)
            ·
              refine ⟨18735912549737135110890803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12490608366491423407260535 18735912549737135110890803)
              ·
                refine ⟨28103868824605702666336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18735912549737135110890803 28103868824605702666336205)
                ·
                  refine ⟨10538950809227138499876077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28103868824605702666336205 10538950809227138499876077)
                  ·
                    refine ⟨3952106553460176937453529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10538950809227138499876077 3952106553460176937453529)
                    ·
                      refine ⟨2964079915095132703090147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952106553460176937453529 2964079915095132703090147)
                      ·
                        rfl

theorem cell23_5772525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5772525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772525 prefixEnd_5772525 := by exact prefixLift 5772525
  have htrace : WordTrace (prefixWord ++ tailWord_5772525) baseStart_5772525 baseEnd_5772525 := by
    simpa [prefixWord, tailWord_5772525, baseEnd_5772525] using wordTrace_append hprefix tailTrace_5772525
  have hstable : (prefixWord ++ tailWord_5772525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772525).length < 2 ^ (prefixWord ++ tailWord_5772525).sum := by decide
  have hdescent : baseEnd_5772525 < baseStart_5772525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772538 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_5772538 : Nat := 118140960795 + 5772538 * 2 ^ 59
def prefixEnd_5772538 : Nat := 4983230072969 + 3 ^ 40 * 5772538 * 2
def baseEnd_5772538 : Nat := 2964086590343641152227587

theorem tailTrace_5772538 : CollatzResearch.WordTrace tailWord_5772538 prefixEnd_5772538 2964086590343641152227587 := by
  unfold tailWord_5772538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635439390272042961577567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140361171707392114564206845 52635439390272042961577567)
  ·
    refine ⟨78953159085408064442366351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52635439390272042961577567 78953159085408064442366351)
    ·
      refine ⟨118429738628112096663549527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78953159085408064442366351 118429738628112096663549527)
      ·
        refine ⟨177644607942168144995324291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118429738628112096663549527 177644607942168144995324291)
        ·
          refine ⟨266466911913252217492986437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177644607942168144995324291 266466911913252217492986437)
          ·
            refine ⟨49962545983734790779934957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266466911913252217492986437 49962545983734790779934957)
            ·
              refine ⟨18735954743900546542475609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49962545983734790779934957 18735954743900546542475609)
              ·
                refine ⟨14051966057925409906856707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18735954743900546542475609 14051966057925409906856707)
                ·
                  refine ⟨21077949086888114860285061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14051966057925409906856707 21077949086888114860285061)
                  ·
                    refine ⟨3952115453791521536303449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21077949086888114860285061 3952115453791521536303449)
                    ·
                      refine ⟨2964086590343641152227587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952115453791521536303449 2964086590343641152227587)
                      ·
                        rfl

theorem cell23_5772538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_5772538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772538 prefixEnd_5772538 := by exact prefixLift 5772538
  have htrace : WordTrace (prefixWord ++ tailWord_5772538) baseStart_5772538 baseEnd_5772538 := by
    simpa [prefixWord, tailWord_5772538, baseEnd_5772538] using wordTrace_append hprefix tailTrace_5772538
  have hstable : (prefixWord ++ tailWord_5772538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772538).length < 2 ^ (prefixWord ++ tailWord_5772538).sum := by decide
  have hdescent : baseEnd_5772538 < baseStart_5772538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772555 : List Nat := [1, 1, 1, 1, 5, 3, 1, 4, 2, 2, 2]
def baseStart_5772555 : Nat := 118140960795 + 5772555 * 2 ^ 59
def prefixEnd_5772555 : Nat := 4983230072969 + 3 ^ 40 * 5772555 * 2
def baseEnd_5772555 : Nat := 2964095319514767585715009

theorem tailTrace_5772555 : CollatzResearch.WordTrace tailWord_5772555 prefixEnd_5772555 2964095319514767585715009 := by
  unfold tailWord_5772555
  simp only [CollatzResearch.WordTrace]
  refine ⟨210542377602026583749679119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140361585068017722499786079 210542377602026583749679119)
  ·
    refine ⟨315813566403039875624518679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210542377602026583749679119 315813566403039875624518679)
    ·
      refine ⟨473720349604559813436778019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315813566403039875624518679 473720349604559813436778019)
      ·
        refine ⟨710580524406839720155167029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473720349604559813436778019 710580524406839720155167029)
        ·
          refine ⟨66616924163141223764546909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 710580524406839720155167029 66616924163141223764546909)
          ·
            refine ⟨24981346561177958911705091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66616924163141223764546909 24981346561177958911705091)
            ·
              refine ⟨37472019841766938367557637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24981346561177958911705091 37472019841766938367557637)
              ·
                refine ⟨7026003720331300943917057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37472019841766938367557637 7026003720331300943917057)
                ·
                  refine ⟨5269502790248475707937793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7026003720331300943917057 5269502790248475707937793)
                  ·
                    refine ⟨3952127092686356780953345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269502790248475707937793 3952127092686356780953345)
                    ·
                      refine ⟨2964095319514767585715009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952127092686356780953345 2964095319514767585715009)
                      ·
                        rfl

theorem cell23_5772555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 2, 2].length) (baseStart_5772555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772555 prefixEnd_5772555 := by exact prefixLift 5772555
  have htrace : WordTrace (prefixWord ++ tailWord_5772555) baseStart_5772555 baseEnd_5772555 := by
    simpa [prefixWord, tailWord_5772555, baseEnd_5772555] using wordTrace_append hprefix tailTrace_5772555
  have hstable : (prefixWord ++ tailWord_5772555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772555).length < 2 ^ (prefixWord ++ tailWord_5772555).sum := by decide
  have hdescent : baseEnd_5772555 < baseStart_5772555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772578 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_5772578 : Nat := 118140960795 + 5772578 * 2 ^ 59
def prefixEnd_5772578 : Nat := 4983230072969 + 3 ^ 40 * 5772578 * 2
def baseEnd_5772578 : Nat := 329345236618868999525267

theorem tailTrace_5772578 : CollatzResearch.WordTrace tailWord_5772578 prefixEnd_5772578 329345236618868999525267 := by
  unfold tailWord_5772578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52635804120235814669441597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140362144320628839118510925 52635804120235814669441597)
  ·
    refine ⟨19738426545088430501040599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52635804120235814669441597 19738426545088430501040599)
    ·
      refine ⟨29607639817632645751560899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19738426545088430501040599 29607639817632645751560899)
      ·
        refine ⟨44411459726448968627341349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29607639817632645751560899 44411459726448968627341349)
        ·
          refine ⟨8327148698709181617626503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44411459726448968627341349 8327148698709181617626503)
          ·
            refine ⟨12490723048063772426439755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8327148698709181617626503 12490723048063772426439755)
            ·
              refine ⟨18736084572095658639659633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12490723048063772426439755 18736084572095658639659633)
              ·
                refine ⟨14052063429071743979744725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18736084572095658639659633 14052063429071743979744725)
                ·
                  refine ⟨329345236618868999525267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14052063429071743979744725 329345236618868999525267)
                  ·
                    rfl

theorem cell23_5772578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_5772578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772578 prefixEnd_5772578 := by exact prefixLift 5772578
  have htrace : WordTrace (prefixWord ++ tailWord_5772578) baseStart_5772578 baseEnd_5772578 := by
    simpa [prefixWord, tailWord_5772578, baseEnd_5772578] using wordTrace_append hprefix tailTrace_5772578
  have hstable : (prefixWord ++ tailWord_5772578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772578).length < 2 ^ (prefixWord ++ tailWord_5772578).sum := by decide
  have hdescent : baseEnd_5772578 < baseStart_5772578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772611 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4]
def baseStart_5772611 : Nat := 118140960795 + 5772611 * 2 ^ 59
def prefixEnd_5772611 : Nat := 4983230072969 + 3 ^ 40 * 5772611 * 2
def baseEnd_5772611 : Nat := 2964124074431419366614751

theorem tailTrace_5772611 : CollatzResearch.WordTrace tailWord_5772611 prefixEnd_5772611 2964124074431419366614751 := by
  unfold tailWord_5772611
  simp only [CollatzResearch.WordTrace]
  refine ⟨210544420089823705313717687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140362946726549136875811791 210544420089823705313717687)
  ·
    refine ⟨315816630134735557970576531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210544420089823705313717687 315816630134735557970576531)
    ·
      refine ⟨473724945202103336955864797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315816630134735557970576531 473724945202103336955864797)
      ·
        refine ⟨177646854450788751358449299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473724945202103336955864797 177646854450788751358449299)
        ·
          refine ⟨266470281676183127037673949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177646854450788751358449299 266470281676183127037673949)
          ·
            refine ⟨99926355628568672639127731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266470281676183127037673949 99926355628568672639127731)
            ·
              refine ⟨149889533442853008958691597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99926355628568672639127731 149889533442853008958691597)
              ·
                refine ⟨56208575041069878359509349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149889533442853008958691597 56208575041069878359509349)
                ·
                  refine ⟨10539107820200602192408003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56208575041069878359509349 10539107820200602192408003)
                  ·
                    refine ⟨15808661730300903288612005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10539107820200602192408003 15808661730300903288612005)
                    ·
                      refine ⟨2964124074431419366614751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15808661730300903288612005 2964124074431419366614751)
                      ·
                        rfl

theorem cell23_5772611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_5772611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772611 prefixEnd_5772611 := by exact prefixLift 5772611
  have htrace : WordTrace (prefixWord ++ tailWord_5772611) baseStart_5772611 baseEnd_5772611 := by
    simpa [prefixWord, tailWord_5772611, baseEnd_5772611] using wordTrace_append hprefix tailTrace_5772611
  have hstable : (prefixWord ++ tailWord_5772611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772611).length < 2 ^ (prefixWord ++ tailWord_5772611).sum := by decide
  have hdescent : baseEnd_5772611 < baseStart_5772611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772698 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_5772698 : Nat := 118140960795 + 5772698 * 2 ^ 59
def prefixEnd_5772698 : Nat := 4983230072969 + 3 ^ 40 * 5772698 * 2
def baseEnd_5772698 : Nat := 988056249082786842075617

theorem tailTrace_5772698 : CollatzResearch.WordTrace tailWord_5772698 prefixEnd_5772698 988056249082786842075617 := by
  unfold tailWord_5772698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52636898310127129793033687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140365062160339012781423165 52636898310127129793033687)
  ·
    refine ⟨78955347465190694689550531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52636898310127129793033687 78955347465190694689550531)
    ·
      refine ⟨118433021197786042034325797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78955347465190694689550531 118433021197786042034325797)
      ·
        refine ⟨22206191474584882881436087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118433021197786042034325797 22206191474584882881436087)
        ·
          refine ⟨33309287211877324322154131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22206191474584882881436087 33309287211877324322154131)
          ·
            refine ⟨49963930817815986483231197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33309287211877324322154131 49963930817815986483231197)
            ·
              refine ⟨18736474056680994931211699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49963930817815986483231197 18736474056680994931211699)
              ·
                refine ⟨28104711085021492396817549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18736474056680994931211699 28104711085021492396817549)
                ·
                  refine ⟨10539266656883059648806581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28104711085021492396817549 10539266656883059648806581)
                  ·
                    refine ⟨988056249082786842075617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10539266656883059648806581 988056249082786842075617)
                    ·
                      rfl

theorem cell23_5772698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_5772698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772698 prefixEnd_5772698 := by exact prefixLift 5772698
  have htrace : WordTrace (prefixWord ++ tailWord_5772698) baseStart_5772698 baseEnd_5772698 := by
    simpa [prefixWord, tailWord_5772698, baseEnd_5772698] using wordTrace_append hprefix tailTrace_5772698
  have hstable : (prefixWord ++ tailWord_5772698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772698).length < 2 ^ (prefixWord ++ tailWord_5772698).sum := by decide
  have hdescent : baseEnd_5772698 < baseStart_5772698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772728 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 4, 4]
def baseStart_5772728 : Nat := 118140960795 + 5772728 * 2 ^ 59
def prefixEnd_5772728 : Nat := 4983230072969 + 3 ^ 40 * 5772728 * 2
def baseEnd_5772728 : Nat := 988061383889331802950571

theorem tailTrace_5772728 : CollatzResearch.WordTrace tailWord_5772728 prefixEnd_5772728 988061383889331802950571 := by
  unfold tailWord_5772728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105274343715199917147863419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140365791620266556197151225 105274343715199917147863419)
  ·
    refine ⟨157911515572799875721795129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105274343715199917147863419 157911515572799875721795129)
    ·
      refine ⟨118433636679599906791346347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157911515572799875721795129 118433636679599906791346347)
      ·
        refine ⟨177650455019399860187019521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118433636679599906791346347 177650455019399860187019521)
        ·
          refine ⟨133237841264549895140264641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177650455019399860187019521 133237841264549895140264641)
          ·
            refine ⟨99928380948412421355198481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133237841264549895140264641 99928380948412421355198481)
            ·
              refine ⟨74946285711309316016398861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99928380948412421355198481 74946285711309316016398861)
              ·
                refine ⟨28104857141740993506149573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74946285711309316016398861 28104857141740993506149573)
                ·
                  refine ⟨5269660714076436282403045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28104857141740993506149573 5269660714076436282403045)
                  ·
                    refine ⟨988061383889331802950571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5269660714076436282403045 988061383889331802950571)
                    ·
                      rfl

theorem cell23_5772728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_5772728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772728 prefixEnd_5772728 := by exact prefixLift 5772728
  have htrace : WordTrace (prefixWord ++ tailWord_5772728) baseStart_5772728 baseEnd_5772728 := by
    simpa [prefixWord, tailWord_5772728, baseEnd_5772728] using wordTrace_append hprefix tailTrace_5772728
  have hstable : (prefixWord ++ tailWord_5772728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772728).length < 2 ^ (prefixWord ++ tailWord_5772728).sum := by decide
  have hdescent : baseEnd_5772728 < baseStart_5772728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772729 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5772729 : Nat := 118140960795 + 5772729 * 2 ^ 59
def prefixEnd_5772729 : Nat := 4983230072969 + 3 ^ 40 * 5772729 * 2
def baseEnd_5772729 : Nat := 2964184665148649904939209

theorem tailTrace_5772729 : CollatzResearch.WordTrace tailWord_5772729 prefixEnd_5772729 2964184665148649904939209 := by
  unfold tailWord_5772729
  simp only [CollatzResearch.WordTrace]
  refine ⟨210548723903396211466513241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140365815935597474311008827 210548723903396211466513241)
  ·
    refine ⟨157911542927547158599884931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210548723903396211466513241 157911542927547158599884931)
    ·
      refine ⟨236867314391320737899827397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157911542927547158599884931 236867314391320737899827397)
      ·
        refine ⟨44412621448372638356217637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236867314391320737899827397 44412621448372638356217637)
        ·
          refine ⟨8327366521569869691790807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44412621448372638356217637 8327366521569869691790807)
          ·
            refine ⟨12491049782354804537686211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8327366521569869691790807 12491049782354804537686211)
            ·
              refine ⟨18736574673532206806529317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491049782354804537686211 18736574673532206806529317)
              ·
                refine ⟨3513107751287288776224247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18736574673532206806529317 3513107751287288776224247)
                ·
                  refine ⟨5269661626930933164336371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513107751287288776224247 5269661626930933164336371)
                  ·
                    refine ⟨7904492440396399746504557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5269661626930933164336371 7904492440396399746504557)
                    ·
                      refine ⟨2964184665148649904939209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7904492440396399746504557 2964184665148649904939209)
                      ·
                        rfl

theorem cell23_5772729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5772729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772729 prefixEnd_5772729 := by exact prefixLift 5772729
  have htrace : WordTrace (prefixWord ++ tailWord_5772729) baseStart_5772729 baseEnd_5772729 := by
    simpa [prefixWord, tailWord_5772729, baseEnd_5772729] using wordTrace_append hprefix tailTrace_5772729
  have hstable : (prefixWord ++ tailWord_5772729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772729).length < 2 ^ (prefixWord ++ tailWord_5772729).sum := by decide
  have hdescent : baseEnd_5772729 < baseStart_5772729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772731 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4]
def baseStart_5772731 : Nat := 118140960795 + 5772731 * 2 ^ 59
def prefixEnd_5772731 : Nat := 4983230072969 + 3 ^ 40 * 5772731 * 2
def baseEnd_5772731 : Nat := 2964185692109958897114199

theorem tailTrace_5772731 : CollatzResearch.WordTrace tailWord_5772731 prefixEnd_5772731 2964185692109958897114199 := by
  unfold tailWord_5772731
  simp only [CollatzResearch.WordTrace]
  refine ⟨210548796849388965808086047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140365864566259310538724031 210548796849388965808086047)
  ·
    refine ⟨315823195274083448712129071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210548796849388965808086047 315823195274083448712129071)
    ·
      refine ⟨473734792911125173068193607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315823195274083448712129071 473734792911125173068193607)
      ·
        refine ⟨710602189366687759602290411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473734792911125173068193607 710602189366687759602290411)
        ·
          refine ⟨1065903284050031639403435617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710602189366687759602290411 1065903284050031639403435617)
          ·
            refine ⟨799427463037523729552576713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065903284050031639403435617 799427463037523729552576713)
            ·
              refine ⟨599570597278142797164432535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799427463037523729552576713 599570597278142797164432535)
              ·
                refine ⟨899355895917214195746648803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599570597278142797164432535 899355895917214195746648803)
                ·
                  refine ⟨1349033843875821293619973205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 899355895917214195746648803 1349033843875821293619973205)
                  ·
                    refine ⟨15808990357919780784609061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1349033843875821293619973205 15808990357919780784609061)
                    ·
                      refine ⟨2964185692109958897114199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15808990357919780784609061 2964185692109958897114199)
                      ·
                        rfl

theorem cell23_5772731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 4].length) (baseStart_5772731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772731 prefixEnd_5772731 := by exact prefixLift 5772731
  have htrace : WordTrace (prefixWord ++ tailWord_5772731) baseStart_5772731 baseEnd_5772731 := by
    simpa [prefixWord, tailWord_5772731, baseEnd_5772731] using wordTrace_append hprefix tailTrace_5772731
  have hstable : (prefixWord ++ tailWord_5772731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772731).length < 2 ^ (prefixWord ++ tailWord_5772731).sum := by decide
  have hdescent : baseEnd_5772731 < baseStart_5772731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772735 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 7, 2, 2]
def baseStart_5772735 : Nat := 118140960795 + 5772735 * 2 ^ 59
def prefixEnd_5772735 : Nat := 4983230072969 + 3 ^ 40 * 5772735 * 2
def baseEnd_5772735 : Nat := 2964187746032576881464181

theorem tailTrace_5772735 : CollatzResearch.WordTrace tailWord_5772735 prefixEnd_5772735 2964187746032576881464181 := by
  unfold tailWord_5772735
  simp only [CollatzResearch.WordTrace]
  refine ⟨210548942741374474491231659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140365961827582982994154439 210548942741374474491231659)
  ·
    refine ⟨315823414112061711736847489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210548942741374474491231659 315823414112061711736847489)
    ·
      refine ⟨236867560584046283802635617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315823414112061711736847489 236867560584046283802635617)
      ·
        refine ⟨177650670438034712851976713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236867560584046283802635617 177650670438034712851976713)
        ·
          refine ⟨133238002828526034638982535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177650670438034712851976713 133238002828526034638982535)
          ·
            refine ⟨199857004242789051958473803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133238002828526034638982535 199857004242789051958473803)
            ·
              refine ⟨299785506364183577937710705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199857004242789051958473803 299785506364183577937710705)
              ·
                refine ⟨224839129773137683453283029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299785506364183577937710705 224839129773137683453283029)
                ·
                  refine ⟨5269667104057914455936321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224839129773137683453283029 5269667104057914455936321)
                  ·
                    refine ⟨3952250328043435841952241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269667104057914455936321 3952250328043435841952241)
                    ·
                      refine ⟨2964187746032576881464181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952250328043435841952241 2964187746032576881464181)
                      ·
                        rfl

theorem cell23_5772735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_5772735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772735 prefixEnd_5772735 := by exact prefixLift 5772735
  have htrace : WordTrace (prefixWord ++ tailWord_5772735) baseStart_5772735 baseEnd_5772735 := by
    simpa [prefixWord, tailWord_5772735, baseEnd_5772735] using wordTrace_append hprefix tailTrace_5772735
  have hstable : (prefixWord ++ tailWord_5772735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772735).length < 2 ^ (prefixWord ++ tailWord_5772735).sum := by decide
  have hdescent : baseEnd_5772735 < baseStart_5772735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772756 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_5772756 : Nat := 118140960795 + 5772756 * 2 ^ 59
def prefixEnd_5772756 : Nat := 4983230072969 + 3 ^ 40 * 5772756 * 2
def baseEnd_5772756 : Nat := 2964198529126321299301585

theorem tailTrace_5772756 : CollatzResearch.WordTrace tailWord_5772756 prefixEnd_5772756 2964198529126321299301585 := by
  unfold tailWord_5772756
  simp only [CollatzResearch.WordTrace]
  refine ⟨105274854337149197538873061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140366472449532263385164081 105274854337149197538873061)
  ·
    refine ⟨19739035188215474538538699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105274854337149197538873061 19739035188215474538538699)
    ·
      refine ⟨29608552782323211807808049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19739035188215474538538699 29608552782323211807808049)
      ·
        refine ⟨22206414586742408855856037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29608552782323211807808049 22206414586742408855856037)
        ·
          refine ⟨4163702735014201660473007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22206414586742408855856037 4163702735014201660473007)
          ·
            refine ⟨6245554102521302490709511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163702735014201660473007 6245554102521302490709511)
            ·
              refine ⟨9368331153781953736064267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245554102521302490709511 9368331153781953736064267)
              ·
                refine ⟨14052496730672930604096401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368331153781953736064267 14052496730672930604096401)
                ·
                  refine ⟨10539372548004697953072301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14052496730672930604096401 10539372548004697953072301)
                  ·
                    refine ⟨3952264705501761732402113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10539372548004697953072301 3952264705501761732402113)
                    ·
                      refine ⟨2964198529126321299301585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952264705501761732402113 2964198529126321299301585)
                      ·
                        rfl

theorem cell23_5772756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_5772756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772756 prefixEnd_5772756 := by exact prefixLift 5772756
  have htrace : WordTrace (prefixWord ++ tailWord_5772756) baseStart_5772756 baseEnd_5772756 := by
    simpa [prefixWord, tailWord_5772756, baseEnd_5772756] using wordTrace_append hprefix tailTrace_5772756
  have hstable : (prefixWord ++ tailWord_5772756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772756).length < 2 ^ (prefixWord ++ tailWord_5772756).sum := by decide
  have hdescent : baseEnd_5772756 < baseStart_5772756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772765 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5772765 : Nat := 118140960795 + 5772765 * 2 ^ 59
def prefixEnd_5772765 : Nat := 4983230072969 + 3 ^ 40 * 5772765 * 2
def baseEnd_5772765 : Nat := 2964203150452211764089043

theorem tailTrace_5772765 : CollatzResearch.WordTrace tailWord_5772765 prefixEnd_5772765 2964203150452211764089043 := by
  unfold tailWord_5772765
  simp only [CollatzResearch.WordTrace]
  refine ⟨210550036931265789614823749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140366691287510526409882499 210550036931265789614823749)
  ·
    refine ⟨39478131924612335552779453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210550036931265789614823749 39478131924612335552779453)
    ·
      refine ⟨14804299471729625832292295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39478131924612335552779453 14804299471729625832292295)
      ·
        refine ⟨22206449207594438748438443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14804299471729625832292295 22206449207594438748438443)
        ·
          refine ⟨33309673811391658122657665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22206449207594438748438443 33309673811391658122657665)
          ·
            refine ⟨24982255358543743591993249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33309673811391658122657665 24982255358543743591993249)
            ·
              refine ⟨18736691518907807693994937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24982255358543743591993249 18736691518907807693994937)
              ·
                refine ⟨14052518639180855770496203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18736691518907807693994937 14052518639180855770496203)
                ·
                  refine ⟨21078777958771283655744305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14052518639180855770496203 21078777958771283655744305)
                  ·
                    refine ⟨15809083469078462741808229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21078777958771283655744305 15809083469078462741808229)
                    ·
                      refine ⟨2964203150452211764089043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15809083469078462741808229 2964203150452211764089043)
                      ·
                        rfl

theorem cell23_5772765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5772765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772765 prefixEnd_5772765 := by exact prefixLift 5772765
  have htrace : WordTrace (prefixWord ++ tailWord_5772765) baseStart_5772765 baseEnd_5772765 := by
    simpa [prefixWord, tailWord_5772765, baseEnd_5772765] using wordTrace_append hprefix tailTrace_5772765
  have hstable : (prefixWord ++ tailWord_5772765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772765).length < 2 ^ (prefixWord ++ tailWord_5772765).sum := by decide
  have hdescent : baseEnd_5772765 < baseStart_5772765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772768 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_5772768 : Nat := 118140960795 + 5772768 * 2 ^ 59
def prefixEnd_5772768 : Nat := 4983230072969 + 3 ^ 40 * 5772768 * 2
def baseEnd_5772768 : Nat := 2964204690894175252351529

theorem tailTrace_5772768 : CollatzResearch.WordTrace tailWord_5772768 prefixEnd_5772768 2964204690894175252351529 := by
  unfold tailWord_5772768
  simp only [CollatzResearch.WordTrace]
  refine ⟨105275073175127460563591479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140366764233503280751455305 105275073175127460563591479)
  ·
    refine ⟨157912609762691190845387219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105275073175127460563591479 157912609762691190845387219)
    ·
      refine ⟨236868914644036786268080829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157912609762691190845387219 236868914644036786268080829)
      ·
        refine ⟨88825842991513794850530311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236868914644036786268080829 88825842991513794850530311)
        ·
          refine ⟨133238764487270692275795467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88825842991513794850530311 133238764487270692275795467)
          ·
            refine ⟨199858146730906038413693201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133238764487270692275795467 199858146730906038413693201)
            ·
              refine ⟨149893610048179528810269901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199858146730906038413693201 149893610048179528810269901)
              ·
                refine ⟨56210103768067323303851213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149893610048179528810269901 56210103768067323303851213)
                ·
                  refine ⟨21078788913025246238944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56210103768067323303851213 21078788913025246238944205)
                  ·
                    refine ⟨7904545842384467339604077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21078788913025246238944205 7904545842384467339604077)
                    ·
                      refine ⟨2964204690894175252351529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7904545842384467339604077 2964204690894175252351529)
                      ·
                        rfl

theorem cell23_5772768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_5772768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772768 prefixEnd_5772768 := by exact prefixLift 5772768
  have htrace : WordTrace (prefixWord ++ tailWord_5772768) baseStart_5772768 baseEnd_5772768 := by
    simpa [prefixWord, tailWord_5772768, baseEnd_5772768] using wordTrace_append hprefix tailTrace_5772768
  have hstable : (prefixWord ++ tailWord_5772768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772768).length < 2 ^ (prefixWord ++ tailWord_5772768).sum := by decide
  have hdescent : baseEnd_5772768 < baseStart_5772768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772769 : List Nat := [1, 2, 3, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_5772769 : Nat := 118140960795 + 5772769 * 2 ^ 59
def prefixEnd_5772769 : Nat := 4983230072969 + 3 ^ 40 * 5772769 * 2
def baseEnd_5772769 : Nat := 2964205204374829748439025

theorem tailTrace_5772769 : CollatzResearch.WordTrace tailWord_5772769 prefixEnd_5772769 2964205204374829748439025 := by
  unfold tailWord_5772769
  simp only [CollatzResearch.WordTrace]
  refine ⟨210550182823251298297969361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140366788548834198865312907 210550182823251298297969361)
  ·
    refine ⟨157912637117438473723477021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210550182823251298297969361 157912637117438473723477021)
    ·
      refine ⟨59217238919039427646303883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157912637117438473723477021 59217238919039427646303883)
      ·
        refine ⟨88825858378559141469455825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59217238919039427646303883 88825858378559141469455825)
        ·
          refine ⟨66619393783919356102091869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88825858378559141469455825 66619393783919356102091869)
          ·
            refine ⟨24982272668969758538284451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66619393783919356102091869 24982272668969758538284451)
            ·
              refine ⟨37473409003454637807426677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24982272668969758538284451 37473409003454637807426677)
              ·
                refine ⟨3513132094073872294446251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37473409003454637807426677 3513132094073872294446251)
                ·
                  refine ⟨5269698141110808441669377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513132094073872294446251 5269698141110808441669377)
                  ·
                    refine ⟨3952273605833106331252033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269698141110808441669377 3952273605833106331252033)
                    ·
                      refine ⟨2964205204374829748439025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952273605833106331252033 2964205204374829748439025)
                      ·
                        rfl

theorem cell23_5772769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_5772769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772769 prefixEnd_5772769 := by exact prefixLift 5772769
  have htrace : WordTrace (prefixWord ++ tailWord_5772769) baseStart_5772769 baseEnd_5772769 := by
    simpa [prefixWord, tailWord_5772769, baseEnd_5772769] using wordTrace_append hprefix tailTrace_5772769
  have hstable : (prefixWord ++ tailWord_5772769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772769).length < 2 ^ (prefixWord ++ tailWord_5772769).sum := by decide
  have hdescent : baseEnd_5772769 < baseStart_5772769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772786 : List Nat := [3, 2, 1, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_5772786 : Nat := 118140960795 + 5772786 * 2 ^ 59
def prefixEnd_5772786 : Nat := 4983230072969 + 3 ^ 40 * 5772786 * 2
def baseEnd_5772786 : Nat := 2964213933545956181926447

theorem tailTrace_5772786 : CollatzResearch.WordTrace tailWord_5772786 prefixEnd_5772786 2964213933545956181926447 := by
  unfold tailWord_5772786
  simp only [CollatzResearch.WordTrace]
  refine ⟨52637700716047427550334553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140367201909459806800892141 52637700716047427550334553)
  ·
    refine ⟨39478275537035570662750915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52637700716047427550334553 39478275537035570662750915)
    ·
      refine ⟨59217413305553355994126373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39478275537035570662750915 59217413305553355994126373)
      ·
        refine ⟨11103264994791254248898695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59217413305553355994126373 11103264994791254248898695)
        ·
          refine ⟨16654897492186881373348043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11103264994791254248898695 16654897492186881373348043)
          ·
            refine ⟨24982346238280322060022065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16654897492186881373348043 24982346238280322060022065)
            ·
              refine ⟨18736759678710241545016549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24982346238280322060022065 18736759678710241545016549)
              ·
                refine ⟨3513142439758170289690603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18736759678710241545016549 3513142439758170289690603)
                ·
                  refine ⟨5269713659637255434535905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513142439758170289690603 5269713659637255434535905)
                  ·
                    refine ⟨3952285244727941575901929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269713659637255434535905 3952285244727941575901929)
                    ·
                      refine ⟨2964213933545956181926447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952285244727941575901929 2964213933545956181926447)
                      ·
                        rfl

theorem cell23_5772786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_5772786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772786 prefixEnd_5772786 := by exact prefixLift 5772786
  have htrace : WordTrace (prefixWord ++ tailWord_5772786) baseStart_5772786 baseEnd_5772786 := by
    simpa [prefixWord, tailWord_5772786, baseEnd_5772786] using wordTrace_append hprefix tailTrace_5772786
  have hstable : (prefixWord ++ tailWord_5772786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772786).length < 2 ^ (prefixWord ++ tailWord_5772786).sum := by decide
  have hdescent : baseEnd_5772786 < baseStart_5772786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772808 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5772808 : Nat := 118140960795 + 5772808 * 2 ^ 59
def prefixEnd_5772808 : Nat := 4983230072969 + 3 ^ 40 * 5772808 * 2
def baseEnd_5772808 : Nat := 2964225230120355095851345

theorem tailTrace_5772808 : CollatzResearch.WordTrace tailWord_5772808 prefixEnd_5772808 2964225230120355095851345 := by
  unfold tailWord_5772808
  simp only [CollatzResearch.WordTrace]
  refine ⟨105275802635055003979319539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140367736846740005305759385 105275802635055003979319539)
  ·
    refine ⟨157913703952582505968979309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105275802635055003979319539 157913703952582505968979309)
    ·
      refine ⟨59217638982218439738367241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157913703952582505968979309 59217638982218439738367241)
      ·
        refine ⟨44413229236663829803775431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59217638982218439738367241 44413229236663829803775431)
        ·
          refine ⟨66619843854995744705663147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44413229236663829803775431 66619843854995744705663147)
          ·
            refine ⟨99929765782493617058494721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66619843854995744705663147 99929765782493617058494721)
            ·
              refine ⟨74947324336870212793871041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99929765782493617058494721 74947324336870212793871041)
              ·
                refine ⟨56210493252652659595403281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74947324336870212793871041 56210493252652659595403281)
                ·
                  refine ⟨42157869939489494696552461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56210493252652659595403281 42157869939489494696552461)
                  ·
                    refine ⟨15809201227308560511207173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42157869939489494696552461 15809201227308560511207173)
                    ·
                      refine ⟨2964225230120355095851345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15809201227308560511207173 2964225230120355095851345)
                      ·
                        rfl

theorem cell23_5772808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5772808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772808 prefixEnd_5772808 := by exact prefixLift 5772808
  have htrace : WordTrace (prefixWord ++ tailWord_5772808) baseStart_5772808 baseEnd_5772808 := by
    simpa [prefixWord, tailWord_5772808, baseEnd_5772808] using wordTrace_append hprefix tailTrace_5772808
  have hstable : (prefixWord ++ tailWord_5772808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772808).length < 2 ^ (prefixWord ++ tailWord_5772808).sum := by decide
  have hdescent : baseEnd_5772808 < baseStart_5772808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772820 : List Nat := [2, 4, 3, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_5772820 : Nat := 118140960795 + 5772820 * 2 ^ 59
def prefixEnd_5772820 : Nat := 4983230072969 + 3 ^ 40 * 5772820 * 2
def baseEnd_5772820 : Nat := 2964231391888209048901291

theorem tailTrace_5772820 : CollatzResearch.WordTrace tailWord_5772820 prefixEnd_5772820 2964231391888209048901291 := by
  unfold tailWord_5772820
  simp only [CollatzResearch.WordTrace]
  refine ⟨105276021473033267004037957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140368028630711022672050609 105276021473033267004037957)
  ·
    refine ⟨19739254026193737563257117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105276021473033267004037957 19739254026193737563257117)
    ·
      refine ⟨7402220259822651586221419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19739254026193737563257117 7402220259822651586221419)
      ·
        refine ⟨11103330389733977379332129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7402220259822651586221419 11103330389733977379332129)
        ·
          refine ⟨8327497792300483034499097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11103330389733977379332129 8327497792300483034499097)
          ·
            refine ⟨6245623344225362275874323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8327497792300483034499097 6245623344225362275874323)
            ·
              refine ⟨9368435016338043413811485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245623344225362275874323 9368435016338043413811485)
              ·
                refine ⟨3513163131126766280179307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9368435016338043413811485 3513163131126766280179307)
                ·
                  refine ⟨5269744696690149420268961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513163131126766280179307 5269744696690149420268961)
                  ·
                    refine ⟨3952308522517612065201721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269744696690149420268961 3952308522517612065201721)
                    ·
                      refine ⟨2964231391888209048901291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952308522517612065201721 2964231391888209048901291)
                      ·
                        rfl

theorem cell23_5772820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_5772820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772820 prefixEnd_5772820 := by exact prefixLift 5772820
  have htrace : WordTrace (prefixWord ++ tailWord_5772820) baseStart_5772820 baseEnd_5772820 := by
    simpa [prefixWord, tailWord_5772820, baseEnd_5772820] using wordTrace_append hprefix tailTrace_5772820
  have hstable : (prefixWord ++ tailWord_5772820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772820).length < 2 ^ (prefixWord ++ tailWord_5772820).sum := by decide
  have hdescent : baseEnd_5772820 < baseStart_5772820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772899 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 5]
def baseStart_5772899 : Nat := 118140960795 + 5772899 * 2 ^ 59
def prefixEnd_5772899 : Nat := 4983230072969 + 3 ^ 40 * 5772899 * 2
def baseEnd_5772899 : Nat := 329363550762212693312603

theorem tailTrace_5772899 : CollatzResearch.WordTrace tailWord_5772899 prefixEnd_5772899 329363550762212693312603 := by
  unfold tailWord_5772899
  simp only [CollatzResearch.WordTrace]
  refine ⟨210554924312780330500201751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140369949541853553666801167 210554924312780330500201751)
  ·
    refine ⟨315832386469170495750302627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210554924312780330500201751 315832386469170495750302627)
    ·
      refine ⟨473748579703755743625453941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315832386469170495750302627 473748579703755743625453941)
      ·
        refine ⟨44413929347227100964886307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 473748579703755743625453941 44413929347227100964886307)
        ·
          refine ⟨66620894020840651447329461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44413929347227100964886307 66620894020840651447329461)
          ·
            refine ⟨6245708814453811073187137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66620894020840651447329461 6245708814453811073187137)
            ·
              refine ⟨4684281610840358304890353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6245708814453811073187137 4684281610840358304890353)
              ·
                refine ⟨3513211208130268728667765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4684281610840358304890353 3513211208130268728667765)
                ·
                  refine ⟨329363550762212693312603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513211208130268728667765 329363550762212693312603)
                  ·
                    rfl

theorem cell23_5772899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 5].length) (baseStart_5772899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772899 prefixEnd_5772899 := by exact prefixLift 5772899
  have htrace : WordTrace (prefixWord ++ tailWord_5772899) baseStart_5772899 baseEnd_5772899 := by
    simpa [prefixWord, tailWord_5772899, baseEnd_5772899] using wordTrace_append hprefix tailTrace_5772899
  have hstable : (prefixWord ++ tailWord_5772899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772899).length < 2 ^ (prefixWord ++ tailWord_5772899).sum := by decide
  have hdescent : baseEnd_5772899 < baseStart_5772899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772908 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 8]
def baseStart_5772908 : Nat := 118140960795 + 5772908 * 2 ^ 59
def prefixEnd_5772908 : Nat := 4983230072969 + 3 ^ 40 * 5772908 * 2
def baseEnd_5772908 : Nat := 988092192728601568200295

theorem tailTrace_5772908 : CollatzResearch.WordTrace tailWord_5772908 prefixEnd_5772908 988092192728601568200295 := by
  unfold tailWord_5772908
  simp only [CollatzResearch.WordTrace]
  refine ⟨105277626284873862518639689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140370168379831816691519585 105277626284873862518639689)
  ·
    refine ⟨78958219713655396888979767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105277626284873862518639689 78958219713655396888979767)
    ·
      refine ⟨118437329570483095333469651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78958219713655396888979767 118437329570483095333469651)
      ·
        refine ⟨177655994355724643000204477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118437329570483095333469651 177655994355724643000204477)
        ·
          refine ⟨66620997883396741125076679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177655994355724643000204477 66620997883396741125076679)
          ·
            refine ⟨99931496825095111687615019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66620997883396741125076679 99931496825095111687615019)
            ·
              refine ⟨149897245237642667531422529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99931496825095111687615019 149897245237642667531422529)
              ·
                refine ⟨112422933928232000648566897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149897245237642667531422529 112422933928232000648566897)
                ·
                  refine ⟨84317200446174000486425173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112422933928232000648566897 84317200446174000486425173)
                  ·
                    refine ⟨988092192728601568200295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84317200446174000486425173 988092192728601568200295)
                    ·
                      rfl

theorem cell23_5772908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_5772908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772908 prefixEnd_5772908 := by exact prefixLift 5772908
  have htrace : WordTrace (prefixWord ++ tailWord_5772908) baseStart_5772908 baseEnd_5772908 := by
    simpa [prefixWord, tailWord_5772908, baseEnd_5772908] using wordTrace_append hprefix tailTrace_5772908
  have hstable : (prefixWord ++ tailWord_5772908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772908).length < 2 ^ (prefixWord ++ tailWord_5772908).sum := by decide
  have hdescent : baseEnd_5772908 < baseStart_5772908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772932 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5772932 : Nat := 118140960795 + 5772932 * 2 ^ 59
def prefixEnd_5772932 : Nat := 4983230072969 + 3 ^ 40 * 5772932 * 2
def baseEnd_5772932 : Nat := 2964288901721512610700775

theorem tailTrace_5772932 : CollatzResearch.WordTrace tailWord_5772932 prefixEnd_5772932 2964288901721512610700775 := by
  unfold tailWord_5772932
  simp only [CollatzResearch.WordTrace]
  refine ⟨105278063960830388568076525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140370751947773851424102033 105278063960830388568076525)
  ·
    refine ⟨39479273985311395713028697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105278063960830388568076525 39479273985311395713028697)
    ·
      refine ⟨29609455488983546784771523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39479273985311395713028697 29609455488983546784771523)
      ·
        refine ⟨44414183233475320177157285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29609455488983546784771523 44414183233475320177157285)
        ·
          refine ⟨8327659356276622533216991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44414183233475320177157285 8327659356276622533216991)
          ·
            refine ⟨12491489034414933799825487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8327659356276622533216991 12491489034414933799825487)
            ·
              refine ⟨18737233551622400699738231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491489034414933799825487 18737233551622400699738231)
              ·
                refine ⟨28105850327433601049607347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18737233551622400699738231 28105850327433601049607347)
                ·
                  refine ⟨42158775491150401574411021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28105850327433601049607347 42158775491150401574411021)
                  ·
                    refine ⟨15809540809181400590404133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42158775491150401574411021 15809540809181400590404133)
                    ·
                      refine ⟨2964288901721512610700775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15809540809181400590404133 2964288901721512610700775)
                      ·
                        rfl

theorem cell23_5772932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5772932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772932 prefixEnd_5772932 := by exact prefixLift 5772932
  have htrace : WordTrace (prefixWord ++ tailWord_5772932) baseStart_5772932 baseEnd_5772932 := by
    simpa [prefixWord, tailWord_5772932, baseEnd_5772932] using wordTrace_append hprefix tailTrace_5772932
  have hstable : (prefixWord ++ tailWord_5772932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772932).length < 2 ^ (prefixWord ++ tailWord_5772932).sum := by decide
  have hdescent : baseEnd_5772932 < baseStart_5772932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772985 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 3, 5]
def baseStart_5772985 : Nat := 118140960795 + 5772985 * 2 ^ 59
def prefixEnd_5772985 : Nat := 4983230072969 + 3 ^ 40 * 5772985 * 2
def baseEnd_5772985 : Nat := 988105372065400301112677

theorem tailTrace_5772985 : CollatzResearch.WordTrace tailWord_5772985 prefixEnd_5772985 988105372065400301112677 := by
  unfold tailWord_5772985
  simp only [CollatzResearch.WordTrace]
  refine ⟨210558060990468767187832409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140372040660312511458554939 210558060990468767187832409)
  ·
    refine ⟨157918545742851575390874307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210558060990468767187832409 157918545742851575390874307)
    ·
      refine ⟨236877818614277363086311461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157918545742851575390874307 236877818614277363086311461)
      ·
        refine ⟨44414590990177005578683399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 236877818614277363086311461 44414590990177005578683399)
        ·
          refine ⟨66621886485265508368025099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44414590990177005578683399 66621886485265508368025099)
          ·
            refine ⟨99932829727898262552037649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66621886485265508368025099 99932829727898262552037649)
            ·
              refine ⟨74949622295923696914028237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99932829727898262552037649 74949622295923696914028237)
              ·
                refine ⟨28106108360971386342760589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74949622295923696914028237 28106108360971386342760589)
                ·
                  refine ⟨10539790635364269878535221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28106108360971386342760589 10539790635364269878535221)
                  ·
                    refine ⟨988105372065400301112677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10539790635364269878535221 988105372065400301112677)
                    ·
                      rfl

theorem cell23_5772985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_5772985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772985 prefixEnd_5772985 := by exact prefixLift 5772985
  have htrace : WordTrace (prefixWord ++ tailWord_5772985) baseStart_5772985 baseEnd_5772985 := by
    simpa [prefixWord, tailWord_5772985, baseEnd_5772985] using wordTrace_append hprefix tailTrace_5772985
  have hstable : (prefixWord ++ tailWord_5772985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772985).length < 2 ^ (prefixWord ++ tailWord_5772985).sum := by decide
  have hdescent : baseEnd_5772985 < baseStart_5772985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5772992 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2]
def baseStart_5772992 : Nat := 118140960795 + 5772992 * 2 ^ 59
def prefixEnd_5772992 : Nat := 4983230072969 + 3 ^ 40 * 5772992 * 2
def baseEnd_5772992 : Nat := 2964319710560782375950499

theorem tailTrace_5772992 : CollatzResearch.WordTrace tailWord_5772992 prefixEnd_5772992 2964319710560782375950499 := by
  unfold tailWord_5772992
  simp only [CollatzResearch.WordTrace]
  refine ⟨105279158150721703691668615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140372210867628938255558153 105279158150721703691668615)
  ·
    refine ⟨157918737226082555537502923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105279158150721703691668615 157918737226082555537502923)
    ·
      refine ⟨236878105839123833306254385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157918737226082555537502923 236878105839123833306254385)
      ·
        refine ⟨177658579379342874979690789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236878105839123833306254385 177658579379342874979690789)
        ·
          refine ⟨33310983633626789058692023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177658579379342874979690789 33310983633626789058692023)
          ·
            refine ⟨49966475450440183588038035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33310983633626789058692023 49966475450440183588038035)
            ·
              refine ⟨74949713175660275382057053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49966475450440183588038035 74949713175660275382057053)
              ·
                refine ⟨28106142440872603268271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74949713175660275382057053 28106142440872603268271395)
                ·
                  refine ⟨42159213661308904902407093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28106142440872603268271395 42159213661308904902407093)
                  ·
                    refine ⟨3952426280747709834600665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42159213661308904902407093 3952426280747709834600665)
                    ·
                      refine ⟨2964319710560782375950499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952426280747709834600665 2964319710560782375950499)
                      ·
                        rfl

theorem cell23_5772992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 1, 5, 2].length) (baseStart_5772992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5772992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5772992 prefixEnd_5772992 := by exact prefixLift 5772992
  have htrace : WordTrace (prefixWord ++ tailWord_5772992) baseStart_5772992 baseEnd_5772992 := by
    simpa [prefixWord, tailWord_5772992, baseEnd_5772992] using wordTrace_append hprefix tailTrace_5772992
  have hstable : (prefixWord ++ tailWord_5772992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5772992).length < 2 ^ (prefixWord ++ tailWord_5772992).sum := by decide
  have hdescent : baseEnd_5772992 < baseStart_5772992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5772992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773009 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_5773009 : Nat := 118140960795 + 5773009 * 2 ^ 59
def prefixEnd_5773009 : Nat := 4983230072969 + 3 ^ 40 * 5773009 * 2
def baseEnd_5773009 : Nat := 2964328439731908809437921

theorem tailTrace_5773009 : CollatzResearch.WordTrace tailWord_5773009 prefixEnd_5773009 2964328439731908809437921 := by
  unfold tailWord_5773009
  simp only [CollatzResearch.WordTrace]
  refine ⟨210558936342381819286706081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140372624228254546191137387 210558936342381819286706081)
  ·
    refine ⟨157919202256786364465029561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210558936342381819286706081 157919202256786364465029561)
    ·
      refine ⟨118439401692589773348772171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157919202256786364465029561 118439401692589773348772171)
      ·
        refine ⟨177659102538884660023158257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118439401692589773348772171 177659102538884660023158257)
        ·
          refine ⟨133244326904163495017368693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177659102538884660023158257 133244326904163495017368693)
          ·
            refine ⟨12491655647265327657878315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133244326904163495017368693 12491655647265327657878315)
            ·
              refine ⟨18737483470897991486817473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12491655647265327657878315 18737483470897991486817473)
              ·
                refine ⟨14053112603173493615113105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18737483470897991486817473 14053112603173493615113105)
                ·
                  refine ⟨10539834452380120211334829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14053112603173493615113105 10539834452380120211334829)
                  ·
                    refine ⟨3952437919642545079250561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10539834452380120211334829 3952437919642545079250561)
                    ·
                      refine ⟨2964328439731908809437921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952437919642545079250561 2964328439731908809437921)
                      ·
                        rfl

theorem cell23_5773009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_5773009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773009 prefixEnd_5773009 := by exact prefixLift 5773009
  have htrace : WordTrace (prefixWord ++ tailWord_5773009) baseStart_5773009 baseEnd_5773009 := by
    simpa [prefixWord, tailWord_5773009, baseEnd_5773009] using wordTrace_append hprefix tailTrace_5773009
  have hstable : (prefixWord ++ tailWord_5773009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773009).length < 2 ^ (prefixWord ++ tailWord_5773009).sum := by decide
  have hdescent : baseEnd_5773009 < baseStart_5773009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773035 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6]
def baseStart_5773035 : Nat := 118140960795 + 5773035 * 2 ^ 59
def prefixEnd_5773035 : Nat := 4983230072969 + 3 ^ 40 * 5773035 * 2
def baseEnd_5773035 : Nat := 2964341790228925707712801

theorem tailTrace_5773035 : CollatzResearch.WordTrace tailWord_5773035 prefixEnd_5773035 2964341790228925707712801 := by
  unfold tailWord_5773035
  simp only [CollatzResearch.WordTrace]
  refine ⟨210559884640287625727152559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140373256426858417151435039 210559884640287625727152559)
  ·
    refine ⟨315839826960431438590728839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210559884640287625727152559 315839826960431438590728839)
    ·
      refine ⟨473759740440647157886093259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315839826960431438590728839 473759740440647157886093259)
      ·
        refine ⟨710639610660970736829139889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473759740440647157886093259 710639610660970736829139889)
        ·
          refine ⟨532979707995728052621854917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710639610660970736829139889 532979707995728052621854917)
          ·
            refine ⟨99933695249199009866597797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 532979707995728052621854917 99933695249199009866597797)
            ·
              refine ⟨18737567859224814349987087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99933695249199009866597797 18737567859224814349987087)
              ·
                refine ⟨28106351788837221524980631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18737567859224814349987087 28106351788837221524980631)
                ·
                  refine ⟨42159527683255832287470947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28106351788837221524980631 42159527683255832287470947)
                  ·
                    refine ⟨63239291524883748431206421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42159527683255832287470947 63239291524883748431206421)
                    ·
                      refine ⟨2964341790228925707712801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63239291524883748431206421 2964341790228925707712801)
                      ·
                        rfl

theorem cell23_5773035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 6].length) (baseStart_5773035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773035 prefixEnd_5773035 := by exact prefixLift 5773035
  have htrace : WordTrace (prefixWord ++ tailWord_5773035) baseStart_5773035 baseEnd_5773035 := by
    simpa [prefixWord, tailWord_5773035, baseEnd_5773035] using wordTrace_append hprefix tailTrace_5773035
  have hstable : (prefixWord ++ tailWord_5773035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773035).length < 2 ^ (prefixWord ++ tailWord_5773035).sum := by decide
  have hdescent : baseEnd_5773035 < baseStart_5773035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773039 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 5, 2, 2]
def baseStart_5773039 : Nat := 118140960795 + 5773039 * 2 ^ 59
def prefixEnd_5773039 : Nat := 4983230072969 + 3 ^ 40 * 5773039 * 2
def baseEnd_5773039 : Nat := 2964343844151543692062783

theorem tailTrace_5773039 : CollatzResearch.WordTrace tailWord_5773039 prefixEnd_5773039 2964343844151543692062783 := by
  unfold tailWord_5773039
  simp only [CollatzResearch.WordTrace]
  refine ⟨210560030532273134410298171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140373353688182089606865447 210560030532273134410298171)
  ·
    refine ⟨315840045798409701615447257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210560030532273134410298171 315840045798409701615447257)
    ·
      refine ⟨236880034348807276211585443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315840045798409701615447257 236880034348807276211585443)
      ·
        refine ⟨355320051523210914317378165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236880034348807276211585443 355320051523210914317378165)
        ·
          refine ⟨33311254830301023217254203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 355320051523210914317378165 33311254830301023217254203)
          ·
            refine ⟨49966882245451534825881305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33311254830301023217254203 49966882245451534825881305)
            ·
              refine ⟨37475161684088651119410979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49966882245451534825881305 37475161684088651119410979)
              ·
                refine ⟨56212742526132976679116469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37475161684088651119410979 56212742526132976679116469)
                ·
                  refine ⟨5269944611824966563667169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56212742526132976679116469 5269944611824966563667169)
                  ·
                    refine ⟨3952458458868724922750377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5269944611824966563667169 3952458458868724922750377)
                    ·
                      refine ⟨2964343844151543692062783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952458458868724922750377 2964343844151543692062783)
                      ·
                        rfl

theorem cell23_5773039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 2, 2].length) (baseStart_5773039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773039 prefixEnd_5773039 := by exact prefixLift 5773039
  have htrace : WordTrace (prefixWord ++ tailWord_5773039) baseStart_5773039 baseEnd_5773039 := by
    simpa [prefixWord, tailWord_5773039, baseEnd_5773039] using wordTrace_append hprefix tailTrace_5773039
  have hstable : (prefixWord ++ tailWord_5773039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773039).length < 2 ^ (prefixWord ++ tailWord_5773039).sum := by decide
  have hdescent : baseEnd_5773039 < baseStart_5773039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773052 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_5773052 : Nat := 118140960795 + 5773052 * 2 ^ 59
def prefixEnd_5773052 : Nat := 4983230072969 + 3 ^ 40 * 5773052 * 2
def baseEnd_5773052 : Nat := 2964350519400052141200223

theorem tailTrace_5773052 : CollatzResearch.WordTrace tailWord_5773052 prefixEnd_5773052 2964350519400052141200223 := by
  unfold tailWord_5773052
  simp only [CollatzResearch.WordTrace]
  refine ⟨105280252340613018815260705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140373669787484025087014273 105280252340613018815260705)
  ·
    refine ⟨78960189255459764111445529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105280252340613018815260705 78960189255459764111445529)
    ·
      refine ⟨59220141941594823083584147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78960189255459764111445529 59220141941594823083584147)
      ·
        refine ⟨88830212912392234625376221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59220141941594823083584147 88830212912392234625376221)
        ·
          refine ⟨33311329842147087984516083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88830212912392234625376221 33311329842147087984516083)
          ·
            refine ⟨49966994763220631976774125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33311329842147087984516083 49966994763220631976774125)
            ·
              refine ⟨18737623036207736991290297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49966994763220631976774125 18737623036207736991290297)
              ·
                refine ⟨14053217277155802743467723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18737623036207736991290297 14053217277155802743467723)
                ·
                  refine ⟨21079825915733704115201585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053217277155802743467723 21079825915733704115201585)
                  ·
                    refine ⟨15809869436800278086401189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21079825915733704115201585 15809869436800278086401189)
                    ·
                      refine ⟨2964350519400052141200223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15809869436800278086401189 2964350519400052141200223)
                      ·
                        rfl

theorem cell23_5773052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_5773052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773052 prefixEnd_5773052 := by exact prefixLift 5773052
  have htrace : WordTrace (prefixWord ++ tailWord_5773052) baseStart_5773052 baseEnd_5773052 := by
    simpa [prefixWord, tailWord_5773052, baseEnd_5773052] using wordTrace_append hprefix tailTrace_5773052
  have hstable : (prefixWord ++ tailWord_5773052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773052).length < 2 ^ (prefixWord ++ tailWord_5773052).sum := by decide
  have hdescent : baseEnd_5773052 < baseStart_5773052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773089 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_5773089 : Nat := 118140960795 + 5773089 * 2 ^ 59
def prefixEnd_5773089 : Nat := 4983230072969 + 3 ^ 40 * 5773089 * 2
def baseEnd_5773089 : Nat := 2964369518184268496437553

theorem tailTrace_5773089 : CollatzResearch.WordTrace tailWord_5773089 prefixEnd_5773089 2964369518184268496437553 := by
  unfold tailWord_5773089
  simp only [CollatzResearch.WordTrace]
  refine ⟨210561854182091992949618321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140374569454727995299745547 210561854182091992949618321)
  ·
    refine ⟨157921390636568994712213741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210561854182091992949618321 157921390636568994712213741)
    ·
      refine ⟨59220521488713373017080153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157921390636568994712213741 59220521488713373017080153)
      ·
        refine ⟨44415391116535029762810115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59220521488713373017080153 44415391116535029762810115)
        ·
          refine ⟨66623086674802544644215173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44415391116535029762810115 66623086674802544644215173)
          ·
            refine ⟨12491828751525477120790345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66623086674802544644215173 12491828751525477120790345)
            ·
              refine ⟨9368871563644107840592759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12491828751525477120790345 9368871563644107840592759)
              ·
                refine ⟨14053307345466161760889139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368871563644107840592759 14053307345466161760889139)
                ·
                  refine ⟨21079961018199242641333709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053307345466161760889139 21079961018199242641333709)
                  ·
                    refine ⟨7904985381824715990500141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21079961018199242641333709 7904985381824715990500141)
                    ·
                      refine ⟨2964369518184268496437553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7904985381824715990500141 2964369518184268496437553)
                      ·
                        rfl

theorem cell23_5773089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_5773089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773089 prefixEnd_5773089 := by exact prefixLift 5773089
  have htrace : WordTrace (prefixWord ++ tailWord_5773089) baseStart_5773089 baseEnd_5773089 := by
    simpa [prefixWord, tailWord_5773089, baseEnd_5773089] using wordTrace_append hprefix tailTrace_5773089
  have hstable : (prefixWord ++ tailWord_5773089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773089).length < 2 ^ (prefixWord ++ tailWord_5773089).sum := by decide
  have hdescent : baseEnd_5773089 < baseStart_5773089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773110 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5773110 : Nat := 118140960795 + 5773110 * 2 ^ 59
def prefixEnd_5773110 : Nat := 4983230072969 + 3 ^ 40 * 5773110 * 2
def baseEnd_5773110 : Nat := 2964380301278012914274957

theorem tailTrace_5773110 : CollatzResearch.WordTrace tailWord_5773110 prefixEnd_5773110 2964380301278012914274957 := by
  unfold tailWord_5773110
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160163757188494596008299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140375080076677275690755189 13160163757188494596008299)
  ·
    refine ⟨19740245635782741894012449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160163757188494596008299 19740245635782741894012449)
    ·
      refine ⟨14805184226837056420509337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19740245635782741894012449 14805184226837056420509337)
      ·
        refine ⟨11103888170127792315382003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14805184226837056420509337 11103888170127792315382003)
        ·
          refine ⟨16655832255191688473073005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11103888170127792315382003 16655832255191688473073005)
          ·
            refine ⟨6245937095696883177402377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16655832255191688473073005 6245937095696883177402377)
            ·
              refine ⟨4684452821772662383051783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6245937095696883177402377 4684452821772662383051783)
              ·
                refine ⟨7026679232658993574577675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684452821772662383051783 7026679232658993574577675)
                ·
                  refine ⟨10540018848988490361866513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026679232658993574577675 10540018848988490361866513)
                  ·
                    refine ⟨7905014136741367771399885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10540018848988490361866513 7905014136741367771399885)
                    ·
                      refine ⟨2964380301278012914274957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905014136741367771399885 2964380301278012914274957)
                      ·
                        rfl

theorem cell23_5773110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5773110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773110 prefixEnd_5773110 := by exact prefixLift 5773110
  have htrace : WordTrace (prefixWord ++ tailWord_5773110) baseStart_5773110 baseEnd_5773110 := by
    simpa [prefixWord, tailWord_5773110, baseEnd_5773110] using wordTrace_append hprefix tailTrace_5773110
  have hstable : (prefixWord ++ tailWord_5773110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773110).length < 2 ^ (prefixWord ++ tailWord_5773110).sum := by decide
  have hdescent : baseEnd_5773110 < baseStart_5773110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773152 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 7]
def baseStart_5773152 : Nat := 118140960795 + 5773152 * 2 ^ 59
def prefixEnd_5773152 : Nat := 4983230072969 + 3 ^ 40 * 5773152 * 2
def baseEnd_5773152 : Nat := 329377985273944638883307

theorem tailTrace_5773152 : CollatzResearch.WordTrace tailWord_5773152 prefixEnd_5773152 329377985273944638883307 := by
  unfold tailWord_5773152
  simp only [CollatzResearch.WordTrace]
  refine ⟨105282075990431877354580855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140376101320575836472774473 105282075990431877354580855)
  ·
    refine ⟨157923113985647816031871283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105282075990431877354580855 157923113985647816031871283)
    ·
      refine ⟨236884670978471724047806925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157923113985647816031871283 236884670978471724047806925)
      ·
        refine ⟨88831751616926896517927597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236884670978471724047806925 88831751616926896517927597)
        ·
          refine ⟨33311906856347586194222849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88831751616926896517927597 33311906856347586194222849)
          ·
            refine ⟨24983930142260689645667137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33311906856347586194222849 24983930142260689645667137)
            ·
              refine ⟨18737947606695517234250353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24983930142260689645667137 18737947606695517234250353)
              ·
                refine ⟨14053460705021637925687765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18737947606695517234250353 14053460705021637925687765)
                ·
                  refine ⟨329377985273944638883307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14053460705021637925687765 329377985273944638883307)
                  ·
                    rfl

theorem cell23_5773152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 7].length) (baseStart_5773152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773152 prefixEnd_5773152 := by exact prefixLift 5773152
  have htrace : WordTrace (prefixWord ++ tailWord_5773152) baseStart_5773152 baseEnd_5773152 := by
    simpa [prefixWord, tailWord_5773152, baseEnd_5773152] using wordTrace_append hprefix tailTrace_5773152
  have hstable : (prefixWord ++ tailWord_5773152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773152).length < 2 ^ (prefixWord ++ tailWord_5773152).sum := by decide
  have hdescent : baseEnd_5773152 < baseStart_5773152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773189 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_5773189 : Nat := 118140960795 + 5773189 * 2 ^ 59
def prefixEnd_5773189 : Nat := 4983230072969 + 3 ^ 40 * 5773189 * 2
def baseEnd_5773189 : Nat := 2964420866249718105187093

theorem tailTrace_5773189 : CollatzResearch.WordTrace tailWord_5773189 prefixEnd_5773189 2964420866249718105187093 := by
  unfold tailWord_5773189
  simp only [CollatzResearch.WordTrace]
  refine ⟨210565501481729710028258621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140377000987819806685505747 210565501481729710028258621)
  ·
    refine ⟨78962063055648641260596983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210565501481729710028258621 78962063055648641260596983)
    ·
      refine ⟨118443094583472961890895475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78962063055648641260596983 118443094583472961890895475)
      ·
        refine ⟨177664641875209442836343213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118443094583472961890895475 177664641875209442836343213)
        ·
          refine ⟨66624240703203541063628705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177664641875209442836343213 66624240703203541063628705)
          ·
            refine ⟨49968180527402655797721529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66624240703203541063628705 49968180527402655797721529)
            ·
              refine ⟨37476135395551991848291147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49968180527402655797721529 37476135395551991848291147)
              ·
                refine ⟨56214203093327987772436721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37476135395551991848291147 56214203093327987772436721)
                ·
                  refine ⟨42160652319995990829327541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56214203093327987772436721 42160652319995990829327541)
                  ·
                    refine ⟨3952561154999624140249457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42160652319995990829327541 3952561154999624140249457)
                    ·
                      refine ⟨2964420866249718105187093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952561154999624140249457 2964420866249718105187093)
                      ·
                        rfl

theorem cell23_5773189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_5773189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773189 prefixEnd_5773189 := by exact prefixLift 5773189
  have htrace : WordTrace (prefixWord ++ tailWord_5773189) baseStart_5773189 baseEnd_5773189 := by
    simpa [prefixWord, tailWord_5773189, baseEnd_5773189] using wordTrace_append hprefix tailTrace_5773189
  have hstable : (prefixWord ++ tailWord_5773189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773189).length < 2 ^ (prefixWord ++ tailWord_5773189).sum := by decide
  have hdescent : baseEnd_5773189 < baseStart_5773189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773219 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 4, 2]
def baseStart_5773219 : Nat := 118140960795 + 5773219 * 2 ^ 59
def prefixEnd_5773219 : Nat := 4983230072969 + 3 ^ 40 * 5773219 * 2
def baseEnd_5773219 : Nat := 2964436270669352987811955

theorem tailTrace_5773219 : CollatzResearch.WordTrace tailWord_5773219 prefixEnd_5773219 2964436270669352987811955 := by
  unfold tailWord_5773219
  simp only [CollatzResearch.WordTrace]
  refine ⟨210566595671621025151850711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140377730447747350101233807 210566595671621025151850711)
  ·
    refine ⟨315849893507431537727776067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210566595671621025151850711 315849893507431537727776067)
    ·
      refine ⟨473774840261147306591664101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315849893507431537727776067 473774840261147306591664101)
      ·
        refine ⟨88832782548965119985937019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 473774840261147306591664101 88832782548965119985937019)
        ·
          refine ⟨133249173823447679978905529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88832782548965119985937019 133249173823447679978905529)
          ·
            refine ⟨99936880367585759984179147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133249173823447679978905529 99936880367585759984179147)
            ·
              refine ⟨149905320551378639976268721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99936880367585759984179147 149905320551378639976268721)
              ·
                refine ⟨112428990413533979982201541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149905320551378639976268721 112428990413533979982201541)
                ·
                  refine ⟨21080435702537621246662789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112428990413533979982201541 21080435702537621246662789)
                  ·
                    refine ⟨3952581694225803983749273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21080435702537621246662789 3952581694225803983749273)
                    ·
                      refine ⟨2964436270669352987811955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952581694225803983749273 2964436270669352987811955)
                      ·
                        rfl

theorem cell23_5773219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_5773219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773219 prefixEnd_5773219 := by exact prefixLift 5773219
  have htrace : WordTrace (prefixWord ++ tailWord_5773219) baseStart_5773219 baseEnd_5773219 := by
    simpa [prefixWord, tailWord_5773219, baseEnd_5773219] using wordTrace_append hprefix tailTrace_5773219
  have hstable : (prefixWord ++ tailWord_5773219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773219).length < 2 ^ (prefixWord ++ tailWord_5773219).sum := by decide
  have hdescent : baseEnd_5773219 < baseStart_5773219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773270 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_5773270 : Nat := 118140960795 + 5773270 * 2 ^ 59
def prefixEnd_5773270 : Nat := 4983230072969 + 3 ^ 40 * 5773270 * 2
def baseEnd_5773270 : Nat := 2964462458182732288274221

theorem tailTrace_5773270 : CollatzResearch.WordTrace tailWord_5773270 prefixEnd_5773270 2964462458182732288274221 := by
  unfold tailWord_5773270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160528487152266303872329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140378970529624173907971509 13160528487152266303872329)
  ·
    refine ⟨9870396365364199727904247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13160528487152266303872329 9870396365364199727904247)
    ·
      refine ⟨14805594548046299591856371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9870396365364199727904247 14805594548046299591856371)
      ·
        refine ⟨22208391822069449387784557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14805594548046299591856371 22208391822069449387784557)
        ·
          refine ⟨8328146933276043520419209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22208391822069449387784557 8328146933276043520419209)
          ·
            refine ⟨6246110199957032640314407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328146933276043520419209 6246110199957032640314407)
            ·
              refine ⟨9369165299935548960471611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246110199957032640314407 9369165299935548960471611)
              ·
                refine ⟨14053747949903323440707417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369165299935548960471611 14053747949903323440707417)
                ·
                  refine ⟨10540310962427492580530563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14053747949903323440707417 10540310962427492580530563)
                  ·
                    refine ⟨15810466443641238870795845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10540310962427492580530563 15810466443641238870795845)
                    ·
                      refine ⟨2964462458182732288274221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15810466443641238870795845 2964462458182732288274221)
                      ·
                        rfl

theorem cell23_5773270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_5773270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773270 prefixEnd_5773270 := by exact prefixLift 5773270
  have htrace : WordTrace (prefixWord ++ tailWord_5773270) baseStart_5773270 baseEnd_5773270 := by
    simpa [prefixWord, tailWord_5773270, baseEnd_5773270] using wordTrace_append hprefix tailTrace_5773270
  have hstable : (prefixWord ++ tailWord_5773270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773270).length < 2 ^ (prefixWord ++ tailWord_5773270).sum := by decide
  have hdescent : baseEnd_5773270 < baseStart_5773270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773273 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_5773273 : Nat := 118140960795 + 5773273 * 2 ^ 59
def prefixEnd_5773273 : Nat := 4983230072969 + 3 ^ 40 * 5773273 * 2
def baseEnd_5773273 : Nat := 2964463998624695776536707

theorem tailTrace_5773273 : CollatzResearch.WordTrace tailWord_5773273 prefixEnd_5773273 2964463998624695776536707 := by
  unfold tailWord_5773273
  simp only [CollatzResearch.WordTrace]
  refine ⟨210568565213425392374316473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140379043475616928249544315 210568565213425392374316473)
  ·
    refine ⟨157926423910069044280737355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210568565213425392374316473 157926423910069044280737355)
    ·
      refine ⟨236889635865103566421106033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157926423910069044280737355 236889635865103566421106033)
      ·
        refine ⟨177667226898827674815829525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236889635865103566421106033 177667226898827674815829525)
        ·
          refine ⟨8328151260882547256992009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177667226898827674815829525 8328151260882547256992009)
          ·
            refine ⟨6246113445661910442744007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328151260882547256992009 6246113445661910442744007)
            ·
              refine ⟨9369170168492865664116011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246113445661910442744007 9369170168492865664116011)
              ·
                refine ⟨14053755252739298496174017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369170168492865664116011 14053755252739298496174017)
                ·
                  refine ⟨10540316439554473872130513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14053755252739298496174017 10540316439554473872130513)
                  ·
                    refine ⟨7905237329665855404097885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10540316439554473872130513 7905237329665855404097885)
                    ·
                      refine ⟨2964463998624695776536707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905237329665855404097885 2964463998624695776536707)
                      ·
                        rfl

theorem cell23_5773273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_5773273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773273 prefixEnd_5773273 := by exact prefixLift 5773273
  have htrace : WordTrace (prefixWord ++ tailWord_5773273) baseStart_5773273 baseEnd_5773273 := by
    simpa [prefixWord, tailWord_5773273, baseEnd_5773273] using wordTrace_append hprefix tailTrace_5773273
  have hstable : (prefixWord ++ tailWord_5773273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773273).length < 2 ^ (prefixWord ++ tailWord_5773273).sum := by decide
  have hdescent : baseEnd_5773273 < baseStart_5773273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773296 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2]
def baseStart_5773296 : Nat := 118140960795 + 5773296 * 2 ^ 59
def prefixEnd_5773296 : Nat := 4983230072969 + 3 ^ 40 * 5773296 * 2
def baseEnd_5773296 : Nat := 2964475808679749186549101

theorem tailTrace_5773296 : CollatzResearch.WordTrace tailWord_5773296 prefixEnd_5773296 2964475808679749186549101 := by
  unfold tailWord_5773296
  simp only [CollatzResearch.WordTrace]
  refine ⟨105284702046171033651201871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140379602728228044868269161 105284702046171033651201871)
  ·
    refine ⟨157927053069256550476802807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105284702046171033651201871 157927053069256550476802807)
    ·
      refine ⟨236890579603884825715204211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157927053069256550476802807 236890579603884825715204211)
      ·
        refine ⟨355335869405827238572806317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236890579603884825715204211 355335869405827238572806317)
        ·
          refine ⟨133250951027185214464802369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355335869405827238572806317 133250951027185214464802369)
          ·
            refine ⟨99938213270388910848601777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133250951027185214464802369 99938213270388910848601777)
            ·
              refine ⟨74953659952791683136451333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99938213270388910848601777 74953659952791683136451333)
              ·
                refine ⟨14053811241148440588084625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74953659952791683136451333 14053811241148440588084625)
                ·
                  refine ⟨10540358430861330441063469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14053811241148440588084625 10540358430861330441063469)
                  ·
                    refine ⟨3952634411572998915398801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10540358430861330441063469 3952634411572998915398801)
                    ·
                      refine ⟨2964475808679749186549101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952634411572998915398801 2964475808679749186549101)
                      ·
                        rfl

theorem cell23_5773296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 3, 2].length) (baseStart_5773296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773296 prefixEnd_5773296 := by exact prefixLift 5773296
  have htrace : WordTrace (prefixWord ++ tailWord_5773296) baseStart_5773296 baseEnd_5773296 := by
    simpa [prefixWord, tailWord_5773296, baseEnd_5773296] using wordTrace_append hprefix tailTrace_5773296
  have hstable : (prefixWord ++ tailWord_5773296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773296).length < 2 ^ (prefixWord ++ tailWord_5773296).sum := by decide
  have hdescent : baseEnd_5773296 < baseStart_5773296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773309 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_5773309 : Nat := 118140960795 + 5773309 * 2 ^ 59
def prefixEnd_5773309 : Nat := 4983230072969 + 3 ^ 40 * 5773309 * 2
def baseEnd_5773309 : Nat := 2964482483928257635686541

theorem tailTrace_5773309 : CollatzResearch.WordTrace tailWord_5773309 prefixEnd_5773309 2964482483928257635686541 := by
  unfold tailWord_5773309
  simp only [CollatzResearch.WordTrace]
  refine ⟨210569878241294970522626981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140379918827529980348417987 210569878241294970522626981)
  ·
    refine ⟨39481852170242806972992559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210569878241294970522626981 39481852170242806972992559)
    ·
      refine ⟨59222778255364210459488839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39481852170242806972992559 59222778255364210459488839)
      ·
        refine ⟨88834167383046315689233259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59222778255364210459488839 88834167383046315689233259)
        ·
          refine ⟨133251251074569473533849889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88834167383046315689233259 133251251074569473533849889)
          ·
            refine ⟨99938438305927105150387417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133251251074569473533849889 99938438305927105150387417)
            ·
              refine ⟨74953828729445328862790563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99938438305927105150387417 74953828729445328862790563)
              ·
                refine ⟨112430743094167993294185845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74953828729445328862790563 112430743094167993294185845)
                ·
                  refine ⟨10540382165078249371329923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112430743094167993294185845 10540382165078249371329923)
                  ·
                    refine ⟨15810573247617374056994885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10540382165078249371329923 15810573247617374056994885)
                    ·
                      refine ⟨2964482483928257635686541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15810573247617374056994885 2964482483928257635686541)
                      ·
                        rfl

theorem cell23_5773309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_5773309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773309 prefixEnd_5773309 := by exact prefixLift 5773309
  have htrace : WordTrace (prefixWord ++ tailWord_5773309) baseStart_5773309 baseEnd_5773309 := by
    simpa [prefixWord, tailWord_5773309, baseEnd_5773309] using wordTrace_append hprefix tailTrace_5773309
  have hstable : (prefixWord ++ tailWord_5773309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773309).length < 2 ^ (prefixWord ++ tailWord_5773309).sum := by decide
  have hdescent : baseEnd_5773309 < baseStart_5773309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773326 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5773326 : Nat := 118140960795 + 5773326 * 2 ^ 59
def prefixEnd_5773326 : Nat := 4983230072969 + 3 ^ 40 * 5773326 * 2
def baseEnd_5773326 : Nat := 2964491213099384069173963

theorem tailTrace_5773326 : CollatzResearch.WordTrace tailWord_5773326 prefixEnd_5773326 2964491213099384069173963 := by
  unfold tailWord_5773326
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321312285279172803249479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140380332188155588283997221 26321312285279172803249479)
  ·
    refine ⟨39481968427918759204874219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321312285279172803249479 39481968427918759204874219)
    ·
      refine ⟨59222952641878138807311329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39481968427918759204874219 59222952641878138807311329)
      ·
        refine ⟨44417214481408604105483497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59222952641878138807311329 44417214481408604105483497)
        ·
          refine ⟨33312910861056453079112623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44417214481408604105483497 33312910861056453079112623)
          ·
            refine ⟨49969366291584679618668935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33312910861056453079112623 49969366291584679618668935)
            ·
              refine ⟨74954049437377019428003403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49969366291584679618668935 74954049437377019428003403)
              ·
                refine ⟨112431074156065529142005105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74954049437377019428003403 112431074156065529142005105)
                ·
                  refine ⟨84323305617049146856503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112431074156065529142005105 84323305617049146856503829)
                  ·
                    refine ⟨3952654950799178758898617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84323305617049146856503829 3952654950799178758898617)
                    ·
                      refine ⟨2964491213099384069173963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952654950799178758898617 2964491213099384069173963)
                      ·
                        rfl

theorem cell23_5773326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5773326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773326 prefixEnd_5773326 := by exact prefixLift 5773326
  have htrace : WordTrace (prefixWord ++ tailWord_5773326) baseStart_5773326 baseEnd_5773326 := by
    simpa [prefixWord, tailWord_5773326, baseEnd_5773326] using wordTrace_append hprefix tailTrace_5773326
  have hstable : (prefixWord ++ tailWord_5773326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773326).length < 2 ^ (prefixWord ++ tailWord_5773326).sum := by decide
  have hdescent : baseEnd_5773326 < baseStart_5773326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773346 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_5773346 : Nat := 118140960795 + 5773346 * 2 ^ 59
def prefixEnd_5773346 : Nat := 4983230072969 + 3 ^ 40 * 5773346 * 2
def baseEnd_5773346 : Nat := 2964501482712473990923871

theorem tailTrace_5773346 : CollatzResearch.WordTrace tailWord_5773346 prefixEnd_5773346 2964501482712473990923871 := by
  unfold tailWord_5773346
  simp only [CollatzResearch.WordTrace]
  refine ⟨52642806935540231460430973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140380818494773950561149261 52642806935540231460430973)
  ·
    refine ⟨19741052600827586797661615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52642806935540231460430973 19741052600827586797661615)
    ·
      refine ⟨29611578901241380196492423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19741052600827586797661615 29611578901241380196492423)
      ·
        refine ⟨44417368351862070294738635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29611578901241380196492423 44417368351862070294738635)
        ·
          refine ⟨66626052527793105442107953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44417368351862070294738635 66626052527793105442107953)
          ·
            refine ⟨49969539395844829081580965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66626052527793105442107953 49969539395844829081580965)
            ·
              refine ⟨9369288636720905452796431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49969539395844829081580965 9369288636720905452796431)
              ·
                refine ⟨14053932955081358179194647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369288636720905452796431 14053932955081358179194647)
                ·
                  refine ⟨21080899432622037268791971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053932955081358179194647 21080899432622037268791971)
                  ·
                    refine ⟨31621349148933055903187957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21080899432622037268791971 31621349148933055903187957)
                    ·
                      refine ⟨2964501482712473990923871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31621349148933055903187957 2964501482712473990923871)
                      ·
                        rfl

theorem cell23_5773346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_5773346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773346 prefixEnd_5773346 := by exact prefixLift 5773346
  have htrace : WordTrace (prefixWord ++ tailWord_5773346) baseStart_5773346 baseEnd_5773346 := by
    simpa [prefixWord, tailWord_5773346, baseEnd_5773346] using wordTrace_append hprefix tailTrace_5773346
  have hstable : (prefixWord ++ tailWord_5773346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773346).length < 2 ^ (prefixWord ++ tailWord_5773346).sum := by decide
  have hdescent : baseEnd_5773346 < baseStart_5773346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773349 : List Nat := [1, 3, 1, 2, 2, 5, 9]
def baseStart_5773349 : Nat := 118140960795 + 5773349 * 2 ^ 59
def prefixEnd_5773349 : Nat := 4983230072969 + 3 ^ 40 * 5773349 * 2
def baseEnd_5773349 : Nat := 36598802754993055298597

theorem tailTrace_5773349 : CollatzResearch.WordTrace tailWord_5773349 prefixEnd_5773349 36598802754993055298597 := by
  unfold tailWord_5773349
  simp only [CollatzResearch.WordTrace]
  refine ⟨210571337161150057354083101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140380891440766704902722067 210571337161150057354083101)
  ·
    refine ⟨78964251435431271507781163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210571337161150057354083101 78964251435431271507781163)
    ·
      refine ⟨118446377153146907261671745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78964251435431271507781163 118446377153146907261671745)
      ·
        refine ⟨88834782864860180446253809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118446377153146907261671745 88834782864860180446253809)
        ·
          refine ⟨66626087148645135334690357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88834782864860180446253809 66626087148645135334690357)
          ·
            refine ⟨6246195670185481437627221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66626087148645135334690357 6246195670185481437627221)
            ·
              refine ⟨36598802754993055298597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6246195670185481437627221 36598802754993055298597)
              ·
                rfl

theorem cell23_5773349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 9].length) (baseStart_5773349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773349 prefixEnd_5773349 := by exact prefixLift 5773349
  have htrace : WordTrace (prefixWord ++ tailWord_5773349) baseStart_5773349 baseEnd_5773349 := by
    simpa [prefixWord, tailWord_5773349, baseEnd_5773349] using wordTrace_append hprefix tailTrace_5773349
  have hstable : (prefixWord ++ tailWord_5773349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773349).length < 2 ^ (prefixWord ++ tailWord_5773349).sum := by decide
  have hdescent : baseEnd_5773349 < baseStart_5773349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773359 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_5773359 : Nat := 118140960795 + 5773359 * 2 ^ 59
def prefixEnd_5773359 : Nat := 4983230072969 + 3 ^ 40 * 5773359 * 2
def baseEnd_5773359 : Nat := 2964508157960982440061311

theorem tailTrace_5773359 : CollatzResearch.WordTrace tailWord_5773359 prefixEnd_5773359 2964508157960982440061311 := by
  unfold tailWord_5773359
  simp only [CollatzResearch.WordTrace]
  refine ⟨210571701891113829061947131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140381134594075886041298087 210571701891113829061947131)
  ·
    refine ⟨315857552836670743592920697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210571701891113829061947131 315857552836670743592920697)
    ·
      refine ⟨236893164627503057694690523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315857552836670743592920697 236893164627503057694690523)
      ·
        refine ⟨355339746941254586542035785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236893164627503057694690523 355339746941254586542035785)
        ·
          refine ⟨266504810205940939906526839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355339746941254586542035785 266504810205940939906526839)
          ·
            refine ⟨399757215308911409859790259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266504810205940939906526839 399757215308911409859790259)
            ·
              refine ⟨599635822963367114789685389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399757215308911409859790259 599635822963367114789685389)
              ·
                refine ⟨224863433611262668046132021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599635822963367114789685389 224863433611262668046132021)
                ·
                  refine ⟨21080946901055875129324877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224863433611262668046132021 21080946901055875129324877)
                  ·
                    refine ⟨7905355087895953173496829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21080946901055875129324877 7905355087895953173496829)
                    ·
                      refine ⟨2964508157960982440061311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905355087895953173496829 2964508157960982440061311)
                      ·
                        rfl

theorem cell23_5773359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_5773359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773359 prefixEnd_5773359 := by exact prefixLift 5773359
  have htrace : WordTrace (prefixWord ++ tailWord_5773359) baseStart_5773359 baseEnd_5773359 := by
    simpa [prefixWord, tailWord_5773359, baseEnd_5773359] using wordTrace_append hprefix tailTrace_5773359
  have hstable : (prefixWord ++ tailWord_5773359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773359).length < 2 ^ (prefixWord ++ tailWord_5773359).sum := by decide
  have hdescent : baseEnd_5773359 < baseStart_5773359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773360 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2]
def baseStart_5773360 : Nat := 118140960795 + 5773360 * 2 ^ 59
def prefixEnd_5773360 : Nat := 4983230072969 + 3 ^ 40 * 5773360 * 2
def baseEnd_5773360 : Nat := 2964508671441636936148807

theorem tailTrace_5773360 : CollatzResearch.WordTrace tailWord_5773360 prefixEnd_5773360 2964508671441636936148807 := by
  unfold tailWord_5773360
  simp only [CollatzResearch.WordTrace]
  refine ⟨105285869182055103116366767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140381158909406804155155689 105285869182055103116366767)
  ·
    refine ⟨157928803773082654674550151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105285869182055103116366767 157928803773082654674550151)
    ·
      refine ⟨236893205659623982011825227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157928803773082654674550151 236893205659623982011825227)
      ·
        refine ⟨355339808489435973017737841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236893205659623982011825227 355339808489435973017737841)
        ·
          refine ⟨266504856367076979763303381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355339808489435973017737841 266504856367076979763303381)
          ·
            refine ⟨6246207571103366713202423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 266504856367076979763303381 6246207571103366713202423)
            ·
              refine ⟨9369311356655050069803635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246207571103366713202423 9369311356655050069803635)
              ·
                refine ⟨14053967034982575104705453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369311356655050069803635 14053967034982575104705453)
                ·
                  refine ⟨5270237638118465664264545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14053967034982575104705453 5270237638118465664264545)
                  ·
                    refine ⟨3952678228588849248198409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270237638118465664264545 3952678228588849248198409)
                    ·
                      refine ⟨2964508671441636936148807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952678228588849248198409 2964508671441636936148807)
                      ·
                        rfl

theorem cell23_5773360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 2, 2].length) (baseStart_5773360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773360 prefixEnd_5773360 := by exact prefixLift 5773360
  have htrace : WordTrace (prefixWord ++ tailWord_5773360) baseStart_5773360 baseEnd_5773360 := by
    simpa [prefixWord, tailWord_5773360, baseEnd_5773360] using wordTrace_append hprefix tailTrace_5773360
  have hstable : (prefixWord ++ tailWord_5773360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773360).length < 2 ^ (prefixWord ++ tailWord_5773360).sum := by decide
  have hdescent : baseEnd_5773360 < baseStart_5773360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773366 : List Nat := [5, 1, 2, 1, 1, 1, 4, 8]
def baseStart_5773366 : Nat := 118140960795 + 5773366 * 2 ^ 59
def prefixEnd_5773366 : Nat := 4983230072969 + 3 ^ 40 * 5773366 * 2
def baseEnd_5773366 : Nat := 109796731567613478247177

theorem tailTrace_5773366 : CollatzResearch.WordTrace tailWord_5773366 prefixEnd_5773366 109796731567613478247177 := by
  unfold tailWord_5773366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160747325130529328590747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140381304801392312838301301 13160747325130529328590747)
  ·
    refine ⟨19741120987695793992886121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160747325130529328590747 19741120987695793992886121)
    ·
      refine ⟨14805840740771845494664591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19741120987695793992886121 14805840740771845494664591)
      ·
        refine ⟨22208761111157768241996887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14805840740771845494664591 22208761111157768241996887)
        ·
          refine ⟨33313141666736652362995331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22208761111157768241996887 33313141666736652362995331)
          ·
            refine ⟨49969712500104978544492997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33313141666736652362995331 49969712500104978544492997)
            ·
              refine ⟨9369321093769683477092437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49969712500104978544492997 9369321093769683477092437)
              ·
                refine ⟨109796731567613478247177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9369321093769683477092437 109796731567613478247177)
                ·
                  rfl

theorem cell23_5773366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_5773366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773366 prefixEnd_5773366 := by exact prefixLift 5773366
  have htrace : WordTrace (prefixWord ++ tailWord_5773366) baseStart_5773366 baseEnd_5773366 := by
    simpa [prefixWord, tailWord_5773366, baseEnd_5773366] using wordTrace_append hprefix tailTrace_5773366
  have hstable : (prefixWord ++ tailWord_5773366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773366).length < 2 ^ (prefixWord ++ tailWord_5773366).sum := by decide
  have hdescent : baseEnd_5773366 < baseStart_5773366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773409 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_5773409 : Nat := 118140960795 + 5773409 * 2 ^ 59
def prefixEnd_5773409 : Nat := 4983230072969 + 3 ^ 40 * 5773409 * 2
def baseEnd_5773409 : Nat := 988177943997902414812027

theorem tailTrace_5773409 : CollatzResearch.WordTrace tailWord_5773409 prefixEnd_5773409 988177943997902414812027 := by
  unfold tailWord_5773409
  simp only [CollatzResearch.WordTrace]
  refine ⟨210573525540932687601267281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140382350360621791734178187 210573525540932687601267281)
  ·
    refine ⟨157930144155699515700950461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210573525540932687601267281 157930144155699515700950461)
    ·
      refine ⟨59223804058387318387856423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157930144155699515700950461 59223804058387318387856423)
      ·
        refine ⟨88835706087580977581784635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59223804058387318387856423 88835706087580977581784635)
        ·
          refine ⟨133253559131371466372676953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88835706087580977581784635 133253559131371466372676953)
          ·
            refine ⟨99940169348528599779507715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133253559131371466372676953 99940169348528599779507715)
            ·
              refine ⟨149910254022792899669261573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99940169348528599779507715 149910254022792899669261573)
              ·
                refine ⟨28108172629273668687986545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149910254022792899669261573 28108172629273668687986545)
                ·
                  refine ⟨21081129471955251515989909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28108172629273668687986545 21081129471955251515989909)
                  ·
                    refine ⟨988177943997902414812027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21081129471955251515989909 988177943997902414812027)
                    ·
                      rfl

theorem cell23_5773409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_5773409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773409 prefixEnd_5773409 := by exact prefixLift 5773409
  have htrace : WordTrace (prefixWord ++ tailWord_5773409) baseStart_5773409 baseEnd_5773409 := by
    simpa [prefixWord, tailWord_5773409, baseEnd_5773409] using wordTrace_append hprefix tailTrace_5773409
  have hstable : (prefixWord ++ tailWord_5773409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773409).length < 2 ^ (prefixWord ++ tailWord_5773409).sum := by decide
  have hdescent : baseEnd_5773409 < baseStart_5773409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773426 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_5773426 : Nat := 118140960795 + 5773426 * 2 ^ 59
def prefixEnd_5773426 : Nat := 4983230072969 + 3 ^ 40 * 5773426 * 2
def baseEnd_5773426 : Nat := 988180853721611225974501

theorem tailTrace_5773426 : CollatzResearch.WordTrace tailWord_5773426 prefixEnd_5773426 988180853721611225974501 := by
  unfold tailWord_5773426
  simp only [CollatzResearch.WordTrace]
  refine ⟨52643536395467774876159033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140382763721247399669757421 52643536395467774876159033)
  ·
    refine ⟨39482652296600831157119275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52643536395467774876159033 39482652296600831157119275)
    ·
      refine ⟨59223978444901246735678913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482652296600831157119275 59223978444901246735678913)
      ·
        refine ⟨44417983833675935051759185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59223978444901246735678913 44417983833675935051759185)
        ·
          refine ⟨33313487875256951288819389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44417983833675935051759185 33313487875256951288819389)
          ·
            refine ⟨12492557953221356733307271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33313487875256951288819389 12492557953221356733307271)
            ·
              refine ⟨18738836929832035099960907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492557953221356733307271 18738836929832035099960907)
              ·
                refine ⟨28108255394748052649941361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18738836929832035099960907 28108255394748052649941361)
                ·
                  refine ⟨21081191546061039487456021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28108255394748052649941361 21081191546061039487456021)
                  ·
                    refine ⟨988180853721611225974501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21081191546061039487456021 988180853721611225974501)
                    ·
                      rfl

theorem cell23_5773426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_5773426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773426 prefixEnd_5773426 := by exact prefixLift 5773426
  have htrace : WordTrace (prefixWord ++ tailWord_5773426) baseStart_5773426 baseEnd_5773426 := by
    simpa [prefixWord, tailWord_5773426, baseEnd_5773426] using wordTrace_append hprefix tailTrace_5773426
  have hstable : (prefixWord ++ tailWord_5773426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773426).length < 2 ^ (prefixWord ++ tailWord_5773426).sum := by decide
  have hdescent : baseEnd_5773426 < baseStart_5773426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773433 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 4, 2]
def baseStart_5773433 : Nat := 118140960795 + 5773433 * 2 ^ 59
def prefixEnd_5773433 : Nat := 4983230072969 + 3 ^ 40 * 5773433 * 2
def baseEnd_5773433 : Nat := 2964546155529415150535971

theorem tailTrace_5773433 : CollatzResearch.WordTrace tailWord_5773433 prefixEnd_5773433 2964546155529415150535971 := by
  unfold tailWord_5773433
  simp only [CollatzResearch.WordTrace]
  refine ⟨210574400892845739700140953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140382933928563826466760635 210574400892845739700140953)
  ·
    refine ⟨157930800669634304775105715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210574400892845739700140953 157930800669634304775105715)
    ·
      refine ⟨236896201004451457162658573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157930800669634304775105715 236896201004451457162658573)
      ·
        refine ⟨88836075376669296435996965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236896201004451457162658573 88836075376669296435996965)
        ·
          refine ⟨16656764133125493081749431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88836075376669296435996965 16656764133125493081749431)
          ·
            refine ⟨24985146199688239622624147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16656764133125493081749431 24985146199688239622624147)
            ·
              refine ⟨37477719299532359433936221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24985146199688239622624147 37477719299532359433936221)
              ·
                refine ⟨14054144737324634787726083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37477719299532359433936221 14054144737324634787726083)
                ·
                  refine ⟨21081217105986952181589125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14054144737324634787726083 21081217105986952181589125)
                  ·
                    refine ⟨3952728207372553534047961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21081217105986952181589125 3952728207372553534047961)
                    ·
                      refine ⟨2964546155529415150535971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952728207372553534047961 2964546155529415150535971)
                      ·
                        rfl

theorem cell23_5773433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_5773433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773433 prefixEnd_5773433 := by exact prefixLift 5773433
  have htrace : WordTrace (prefixWord ++ tailWord_5773433) baseStart_5773433 baseEnd_5773433 := by
    simpa [prefixWord, tailWord_5773433, baseEnd_5773433] using wordTrace_append hprefix tailTrace_5773433
  have hstable : (prefixWord ++ tailWord_5773433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773433).length < 2 ^ (prefixWord ++ tailWord_5773433).sum := by decide
  have hdescent : baseEnd_5773433 < baseStart_5773433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773454 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5773454 : Nat := 118140960795 + 5773454 * 2 ^ 59
def prefixEnd_5773454 : Nat := 4983230072969 + 3 ^ 40 * 5773454 * 2
def baseEnd_5773454 : Nat := 2964556938623159568373375

theorem tailTrace_5773454 : CollatzResearch.WordTrace tailWord_5773454 prefixEnd_5773454 2964556938623159568373375 := by
  unfold tailWord_5773454
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321895853221207535831927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140383444550513106857770277 26321895853221207535831927)
  ·
    refine ⟨39482843779831811303747891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321895853221207535831927 39482843779831811303747891)
    ·
      refine ⟨59224265669747716955621837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482843779831811303747891 59224265669747716955621837)
      ·
        refine ⟨22209099626155393858358189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59224265669747716955621837 22209099626155393858358189)
        ·
          refine ⟨8328412359808272696884321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22209099626155393858358189 8328412359808272696884321)
          ·
            refine ⟨6246309269856204522663241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328412359808272696884321 6246309269856204522663241)
            ·
              refine ⟨4684731952392153391997431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246309269856204522663241 4684731952392153391997431)
              ·
                refine ⟨7027097928588230087996147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684731952392153391997431 7027097928588230087996147)
                ·
                  refine ⟨10540646892882345131994221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027097928588230087996147 10540646892882345131994221)
                  ·
                    refine ⟨3952742584830879424497833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10540646892882345131994221 3952742584830879424497833)
                    ·
                      refine ⟨2964556938623159568373375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952742584830879424497833 2964556938623159568373375)
                      ·
                        rfl

theorem cell23_5773454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5773454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773454 prefixEnd_5773454 := by exact prefixLift 5773454
  have htrace : WordTrace (prefixWord ++ tailWord_5773454) baseStart_5773454 baseEnd_5773454 := by
    simpa [prefixWord, tailWord_5773454, baseEnd_5773454] using wordTrace_append hprefix tailTrace_5773454
  have hstable : (prefixWord ++ tailWord_5773454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773454).length < 2 ^ (prefixWord ++ tailWord_5773454).sum := by decide
  have hdescent : baseEnd_5773454 < baseStart_5773454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773473 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 5]
def baseStart_5773473 : Nat := 118140960795 + 5773473 * 2 ^ 59
def prefixEnd_5773473 : Nat := 4983230072969 + 3 ^ 40 * 5773473 * 2
def baseEnd_5773473 : Nat := 329396299417288332670643

theorem tailTrace_5773473 : CollatzResearch.WordTrace tailWord_5773473 prefixEnd_5773473 329396299417288332670643 := by
  unfold tailWord_5773473
  simp only [CollatzResearch.WordTrace]
  refine ⟨210575859812700826531597073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140383906541800551021064715 210575859812700826531597073)
  ·
    refine ⟨157931894859525619898697805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210575859812700826531597073 157931894859525619898697805)
    ·
      refine ⟨59224460572322107462011677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157931894859525619898697805 59224460572322107462011677)
      ·
        refine ⟨22209172714620790298254379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59224460572322107462011677 22209172714620790298254379)
        ·
          refine ⟨33313759071931185447381569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22209172714620790298254379 33313759071931185447381569)
          ·
            refine ⟨24985319303948389085536177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33313759071931185447381569 24985319303948389085536177)
            ·
              refine ⟨18738989477961291814152133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24985319303948389085536177 18738989477961291814152133)
              ·
                refine ⟨3513560527117742215153525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18738989477961291814152133 3513560527117742215153525)
                ·
                  refine ⟨329396299417288332670643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513560527117742215153525 329396299417288332670643)
                  ·
                    rfl

theorem cell23_5773473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 5].length) (baseStart_5773473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773473 prefixEnd_5773473 := by exact prefixLift 5773473
  have htrace : WordTrace (prefixWord ++ tailWord_5773473) baseStart_5773473 baseEnd_5773473 := by
    simpa [prefixWord, tailWord_5773473, baseEnd_5773473] using wordTrace_append hprefix tailTrace_5773473
  have hstable : (prefixWord ++ tailWord_5773473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773473).length < 2 ^ (prefixWord ++ tailWord_5773473).sum := by decide
  have hdescent : baseEnd_5773473 < baseStart_5773473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773499 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 8]
def baseStart_5773499 : Nat := 118140960795 + 5773499 * 2 ^ 59
def prefixEnd_5773499 : Nat := 4983230072969 + 3 ^ 40 * 5773499 * 2
def baseEnd_5773499 : Nat := 988193348417537297436889

theorem tailTrace_5773499 : CollatzResearch.WordTrace tailWord_5773499 prefixEnd_5773499 988193348417537297436889 := by
  unfold tailWord_5773499
  simp only [CollatzResearch.WordTrace]
  refine ⟨210576808110606632972043551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140384538740404421981362367 210576808110606632972043551)
  ·
    refine ⟨315865212165909949458065327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210576808110606632972043551 315865212165909949458065327)
    ·
      refine ⟨473797818248864924187097991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315865212165909949458065327 473797818248864924187097991)
      ·
        refine ⟨710696727373297386280646987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473797818248864924187097991 710696727373297386280646987)
        ·
          refine ⟨1066045091059946079420970481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710696727373297386280646987 1066045091059946079420970481)
          ·
            refine ⟨799533818294959559565727861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066045091059946079420970481 799533818294959559565727861)
            ·
              refine ⟨74956295465152458709286987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 799533818294959559565727861 74956295465152458709286987)
              ·
                refine ⟨112434443197728688063930481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74956295465152458709286987 112434443197728688063930481)
                ·
                  refine ⟨84325832398296516047947861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112434443197728688063930481 84325832398296516047947861)
                  ·
                    refine ⟨988193348417537297436889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84325832398296516047947861 988193348417537297436889)
                    ·
                      rfl

theorem cell23_5773499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_5773499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773499 prefixEnd_5773499 := by exact prefixLift 5773499
  have htrace : WordTrace (prefixWord ++ tailWord_5773499) baseStart_5773499 baseEnd_5773499 := by
    simpa [prefixWord, tailWord_5773499, baseEnd_5773499] using wordTrace_append hprefix tailTrace_5773499
  have hstable : (prefixWord ++ tailWord_5773499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773499).length < 2 ^ (prefixWord ++ tailWord_5773499).sum := by decide
  have hdescent : baseEnd_5773499 < baseStart_5773499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773573 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_5773573 : Nat := 118140960795 + 5773573 * 2 ^ 59
def prefixEnd_5773573 : Nat := 4983230072969 + 3 ^ 40 * 5773573 * 2
def baseEnd_5773573 : Nat := 2964618042821044602785327

theorem tailTrace_5773573 : CollatzResearch.WordTrace tailWord_5773573 prefixEnd_5773573 2964618042821044602785327 := by
  unfold tailWord_5773573
  simp only [CollatzResearch.WordTrace]
  refine ⟨210579507112338543610237373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140386338074892362406824915 210579507112338543610237373)
  ·
    refine ⟨78967315167126953853839015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210579507112338543610237373 78967315167126953853839015)
    ·
      refine ⟨118450972750690430780758523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78967315167126953853839015 118450972750690430780758523)
      ·
        refine ⟨177676459126035646171137785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118450972750690430780758523 177676459126035646171137785)
        ·
          refine ⟨133257344344526734628353339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177676459126035646171137785 133257344344526734628353339)
          ·
            refine ⟨199886016516790101942530009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133257344344526734628353339 199886016516790101942530009)
            ·
              refine ⟨149914512387592576456897507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199886016516790101942530009 149914512387592576456897507)
              ·
                refine ⟨224871768581388864685346261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149914512387592576456897507 224871768581388864685346261)
                ·
                  refine ⟨5270432076126301516062803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224871768581388864685346261 5270432076126301516062803)
                  ·
                    refine ⟨7905648114189452274094205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270432076126301516062803 7905648114189452274094205)
                    ·
                      refine ⟨2964618042821044602785327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905648114189452274094205 2964618042821044602785327)
                      ·
                        rfl

theorem cell23_5773573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_5773573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773573 prefixEnd_5773573 := by exact prefixLift 5773573
  have htrace : WordTrace (prefixWord ++ tailWord_5773573) baseStart_5773573 baseEnd_5773573 := by
    simpa [prefixWord, tailWord_5773573, baseEnd_5773573] using wordTrace_append hprefix tailTrace_5773573
  have hstable : (prefixWord ++ tailWord_5773573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773573).length < 2 ^ (prefixWord ++ tailWord_5773573).sum := by decide
  have hdescent : baseEnd_5773573 < baseStart_5773573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773616 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_5773616 : Nat := 118140960795 + 5773616 * 2 ^ 59
def prefixEnd_5773616 : Nat := 4983230072969 + 3 ^ 40 * 5773616 * 2
def baseEnd_5773616 : Nat := 2964640122489187934547629

theorem tailTrace_5773616 : CollatzResearch.WordTrace tailWord_5773616 prefixEnd_5773616 2964640122489187934547629 := by
  unfold tailWord_5773616
  simp only [CollatzResearch.WordTrace]
  refine ⟨105290537725591380977026351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140387383634121841302701801 105290537725591380977026351)
  ·
    refine ⟨157935806588387071465539527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105290537725591380977026351 157935806588387071465539527)
    ·
      refine ⟨236903709882580607198309291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157935806588387071465539527 236903709882580607198309291)
      ·
        refine ⟨355355564823870910797463937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236903709882580607198309291 355355564823870910797463937)
        ·
          refine ⟨266516673617903183098097953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355355564823870910797463937 266516673617903183098097953)
          ·
            refine ⟨199887505213427387323573465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266516673617903183098097953 199887505213427387323573465)
            ·
              refine ⟨149915628910070540492680099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199887505213427387323573465 149915628910070540492680099)
              ·
                refine ⟨224873443365105810739020149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149915628910070540492680099 224873443365105810739020149)
                ·
                  refine ⟨21081885315478669756783139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 224873443365105810739020149 21081885315478669756783139)
                  ·
                    refine ⟨31622827973218004635174709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21081885315478669756783139 31622827973218004635174709)
                    ·
                      refine ⟨2964640122489187934547629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31622827973218004635174709 2964640122489187934547629)
                      ·
                        rfl

theorem cell23_5773616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_5773616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773616 prefixEnd_5773616 := by exact prefixLift 5773616
  have htrace : WordTrace (prefixWord ++ tailWord_5773616) baseStart_5773616 baseEnd_5773616 := by
    simpa [prefixWord, tailWord_5773616, baseEnd_5773616] using wordTrace_append hprefix tailTrace_5773616
  have hstable : (prefixWord ++ tailWord_5773616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773616).length < 2 ^ (prefixWord ++ tailWord_5773616).sum := by decide
  have hdescent : baseEnd_5773616 < baseStart_5773616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773640 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 2, 4]
def baseStart_5773640 : Nat := 118140960795 + 5773640 * 2 ^ 59
def prefixEnd_5773640 : Nat := 4983230072969 + 3 ^ 40 * 5773640 * 2
def baseEnd_5773640 : Nat := 988217482008298613549173

theorem tailTrace_5773640 : CollatzResearch.WordTrace tailWord_5773640 prefixEnd_5773640 988217482008298613549173 := by
  unfold tailWord_5773640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105290975401547907026463187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140387967202063876035284249 105290975401547907026463187)
  ·
    refine ⟨157936463102321860539694781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105290975401547907026463187 157936463102321860539694781)
    ·
      refine ⟨59226173663370697702385543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157936463102321860539694781 59226173663370697702385543)
      ·
        refine ⟨88839260495056046553578315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59226173663370697702385543 88839260495056046553578315)
        ·
          refine ⟨133258890742584069830367473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88839260495056046553578315 133258890742584069830367473)
          ·
            refine ⟨99944168056938052372775605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133258890742584069830367473 99944168056938052372775605)
            ·
              refine ⟨9369765755337942409947713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99944168056938052372775605 9369765755337942409947713)
              ·
                refine ⟨7027324316503456807460785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9369765755337942409947713 7027324316503456807460785)
                ·
                  refine ⟨5270493237377592605595589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027324316503456807460785 5270493237377592605595589)
                  ·
                    refine ⟨988217482008298613549173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270493237377592605595589 988217482008298613549173)
                    ·
                      rfl

theorem cell23_5773640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_5773640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773640 prefixEnd_5773640 := by exact prefixLift 5773640
  have htrace : WordTrace (prefixWord ++ tailWord_5773640) baseStart_5773640 baseEnd_5773640 := by
    simpa [prefixWord, tailWord_5773640, baseEnd_5773640] using wordTrace_append hprefix tailTrace_5773640
  have hstable : (prefixWord ++ tailWord_5773640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773640).length < 2 ^ (prefixWord ++ tailWord_5773640).sum := by decide
  have hdescent : baseEnd_5773640 < baseStart_5773640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773656 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5773656 : Nat := 118140960795 + 5773656 * 2 ^ 59
def prefixEnd_5773656 : Nat := 4983230072969 + 3 ^ 40 * 5773656 * 2
def baseEnd_5773656 : Nat := 2964660661715367778047445

theorem tailTrace_5773656 : CollatzResearch.WordTrace tailWord_5773656 prefixEnd_5773656 2964660661715367778047445 := by
  unfold tailWord_5773656
  simp only [CollatzResearch.WordTrace]
  refine ⟨105291267185518924392754411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140388356247358565857005881 105291267185518924392754411)
  ·
    refine ⟨157936900778278386589131617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105291267185518924392754411 157936900778278386589131617)
    ·
      refine ⟨118452675583708789941848713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157936900778278386589131617 118452675583708789941848713)
      ·
        refine ⟨88839506687781592456386535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118452675583708789941848713 88839506687781592456386535)
        ·
          refine ⟨133259260031672388684579803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88839506687781592456386535 133259260031672388684579803)
          ·
            refine ⟨199888890047508583026869705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133259260031672388684579803 199888890047508583026869705)
            ·
              refine ⟨149916667535631437270152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199888890047508583026869705 149916667535631437270152279)
              ·
                refine ⟨224875001303447155905228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149916667535631437270152279 224875001303447155905228419)
                ·
                  refine ⟨337312501955170733857842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224875001303447155905228419 337312501955170733857842629)
                  ·
                    refine ⟨63246094116594512598345493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 337312501955170733857842629 63246094116594512598345493)
                    ·
                      refine ⟨2964660661715367778047445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63246094116594512598345493 2964660661715367778047445)
                      ·
                        rfl

theorem cell23_5773656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5773656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773656 prefixEnd_5773656 := by exact prefixLift 5773656
  have htrace : WordTrace (prefixWord ++ tailWord_5773656) baseStart_5773656 baseEnd_5773656 := by
    simpa [prefixWord, tailWord_5773656, baseEnd_5773656] using wordTrace_append hprefix tailTrace_5773656
  have hstable : (prefixWord ++ tailWord_5773656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773656).length < 2 ^ (prefixWord ++ tailWord_5773656).sum := by decide
  have hdescent : baseEnd_5773656 < baseStart_5773656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773680 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3]
def baseStart_5773680 : Nat := 118140960795 + 5773680 * 2 ^ 59
def prefixEnd_5773680 : Nat := 4983230072969 + 3 ^ 40 * 5773680 * 2
def baseEnd_5773680 : Nat := 2964672985251075684147335

theorem tailTrace_5773680 : CollatzResearch.WordTrace tailWord_5773680 prefixEnd_5773680 2964672985251075684147335 := by
  unfold tailWord_5773680
  simp only [CollatzResearch.WordTrace]
  refine ⟨105291704861475450442191247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140388939815300600589588329 105291704861475450442191247)
  ·
    refine ⟨157937557292213175663286871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105291704861475450442191247 157937557292213175663286871)
    ·
      refine ⟨236906335938319763494930307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157937557292213175663286871 236906335938319763494930307)
      ·
        refine ⟨355359503907479645242395461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236906335938319763494930307 355359503907479645242395461)
        ·
          refine ⟨66629906982652433482949149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355359503907479645242395461 66629906982652433482949149)
          ·
            refine ⟨24986215118494662556105931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66629906982652433482949149 24986215118494662556105931)
            ·
              refine ⟨37479322677741993834158897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24986215118494662556105931 37479322677741993834158897)
              ·
                refine ⟨28109492008306495375619173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37479322677741993834158897 28109492008306495375619173)
                ·
                  refine ⟨5270529751557467882928595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28109492008306495375619173 5270529751557467882928595)
                  ·
                    refine ⟨7905794627336201824392893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270529751557467882928595 7905794627336201824392893)
                    ·
                      refine ⟨2964672985251075684147335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905794627336201824392893 2964672985251075684147335)
                      ·
                        rfl

theorem cell23_5773680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_5773680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773680 prefixEnd_5773680 := by exact prefixLift 5773680
  have htrace : WordTrace (prefixWord ++ tailWord_5773680) baseStart_5773680 baseEnd_5773680 := by
    simpa [prefixWord, tailWord_5773680, baseEnd_5773680] using wordTrace_append hprefix tailTrace_5773680
  have hstable : (prefixWord ++ tailWord_5773680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773680).length < 2 ^ (prefixWord ++ tailWord_5773680).sum := by decide
  have hdescent : baseEnd_5773680 < baseStart_5773680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773697 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5773697 : Nat := 118140960795 + 5773697 * 2 ^ 59
def prefixEnd_5773697 : Nat := 4983230072969 + 3 ^ 40 * 5773697 * 2
def baseEnd_5773697 : Nat := 2964681714422202117634757

theorem tailTrace_5773697 : CollatzResearch.WordTrace tailWord_5773697 prefixEnd_5773697 2964681714422202117634757 := by
  unfold tailWord_5773697
  simp only [CollatzResearch.WordTrace]
  refine ⟨210584029763889312787751345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140389353175926208525167563 210584029763889312787751345)
  ·
    refine ⟨157938022322916984590813509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210584029763889312787751345 157938022322916984590813509)
    ·
      refine ⟨29613379185546934610777533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157938022322916984590813509 29613379185546934610777533)
      ·
        refine ⟨11105017194580100479041575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29613379185546934610777533 11105017194580100479041575)
        ·
          refine ⟨16657525791870150718562363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105017194580100479041575 16657525791870150718562363)
          ·
            refine ⟨24986288687805226077843545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16657525791870150718562363 24986288687805226077843545)
            ·
              refine ⟨18739716515853919558382659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24986288687805226077843545 18739716515853919558382659)
              ·
                refine ⟨28109574773780879337573989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18739716515853919558382659 28109574773780879337573989)
                ·
                  refine ⟨5270545270083914875795123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28109574773780879337573989 5270545270083914875795123)
                  ·
                    refine ⟨7905817905125872313692685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270545270083914875795123 7905817905125872313692685)
                    ·
                      refine ⟨2964681714422202117634757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905817905125872313692685 2964681714422202117634757)
                      ·
                        rfl

theorem cell23_5773697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5773697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773697 prefixEnd_5773697 := by exact prefixLift 5773697
  have htrace : WordTrace (prefixWord ++ tailWord_5773697) baseStart_5773697 baseEnd_5773697 := by
    simpa [prefixWord, tailWord_5773697, baseEnd_5773697] using wordTrace_append hprefix tailTrace_5773697
  have hstable : (prefixWord ++ tailWord_5773697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773697).length < 2 ^ (prefixWord ++ tailWord_5773697).sum := by decide
  have hdescent : baseEnd_5773697 < baseStart_5773697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773698 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5773698 : Nat := 118140960795 + 5773698 * 2 ^ 59
def prefixEnd_5773698 : Nat := 4983230072969 + 3 ^ 40 * 5773698 * 2
def baseEnd_5773698 : Nat := 2964682227902856613722253

theorem tailTrace_5773698 : CollatzResearch.WordTrace tailWord_5773698 prefixEnd_5773698 2964682227902856613722253 := by
  unfold tailWord_5773698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52646016559221422489634437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140389377491257126639025165 52646016559221422489634437)
  ·
    refine ⟨9871128104854016716806457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52646016559221422489634437 9871128104854016716806457)
    ·
      refine ⟨7403346078640512537604843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9871128104854016716806457 7403346078640512537604843)
      ·
        refine ⟨11105019117960768806407265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403346078640512537604843 11105019117960768806407265)
        ·
          refine ⟨8328764338470576604805449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11105019117960768806407265 8328764338470576604805449)
          ·
            refine ⟨6246573253852932453604087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328764338470576604805449 6246573253852932453604087)
            ·
              refine ⟨9369859880779398680406131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246573253852932453604087 9369859880779398680406131)
              ·
                refine ⟨14054789821169098020609197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369859880779398680406131 14054789821169098020609197)
                ·
                  refine ⟨5270546182938411757728449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14054789821169098020609197 5270546182938411757728449)
                  ·
                    refine ⟨3952909637203808818296337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270546182938411757728449 3952909637203808818296337)
                    ·
                      refine ⟨2964682227902856613722253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3952909637203808818296337 2964682227902856613722253)
                      ·
                        rfl

theorem cell23_5773698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5773698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773698 prefixEnd_5773698 := by exact prefixLift 5773698
  have htrace : WordTrace (prefixWord ++ tailWord_5773698) baseStart_5773698 baseEnd_5773698 := by
    simpa [prefixWord, tailWord_5773698, baseEnd_5773698] using wordTrace_append hprefix tailTrace_5773698
  have hstable : (prefixWord ++ tailWord_5773698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773698).length < 2 ^ (prefixWord ++ tailWord_5773698).sum := by decide
  have hdescent : baseEnd_5773698 < baseStart_5773698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773703 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_5773703 : Nat := 118140960795 + 5773703 * 2 ^ 59
def prefixEnd_5773703 : Nat := 4983230072969 + 3 ^ 40 * 5773703 * 2
def baseEnd_5773703 : Nat := 2964684795306129094159729

theorem tailTrace_5773703 : CollatzResearch.WordTrace tailWord_5773703 prefixEnd_5773703 2964684795306129094159729 := by
  unfold tailWord_5773703
  simp only [CollatzResearch.WordTrace]
  refine ⟨210584248601867575812469763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140389499067911717208313175 210584248601867575812469763)
  ·
    refine ⟨315876372902801363718704645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210584248601867575812469763 315876372902801363718704645)
    ·
      refine ⟨59226819919275255697257121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 315876372902801363718704645 59226819919275255697257121)
      ·
        refine ⟨44420114939456441772942841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59226819919275255697257121 44420114939456441772942841)
        ·
          refine ⟨33315086204592331329707131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44420114939456441772942841 33315086204592331329707131)
          ·
            refine ⟨49972629306888496994560697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33315086204592331329707131 49972629306888496994560697)
            ·
              refine ⟨37479471980166372745920523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49972629306888496994560697 37479471980166372745920523)
              ·
                refine ⟨56219207970249559118880785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37479471980166372745920523 56219207970249559118880785)
                ·
                  refine ⟨42164405977687169339160589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56219207970249559118880785 42164405977687169339160589)
                  ·
                    refine ⟨15811652241632688502185221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42164405977687169339160589 15811652241632688502185221)
                    ·
                      refine ⟨2964684795306129094159729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15811652241632688502185221 2964684795306129094159729)
                      ·
                        rfl

theorem cell23_5773703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_5773703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773703 prefixEnd_5773703 := by exact prefixLift 5773703
  have htrace : WordTrace (prefixWord ++ tailWord_5773703) baseStart_5773703 baseEnd_5773703 := by
    simpa [prefixWord, tailWord_5773703, baseEnd_5773703] using wordTrace_append hprefix tailTrace_5773703
  have hstable : (prefixWord ++ tailWord_5773703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773703).length < 2 ^ (prefixWord ++ tailWord_5773703).sum := by decide
  have hdescent : baseEnd_5773703 < baseStart_5773703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773748 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_5773748 : Nat := 118140960795 + 5773748 * 2 ^ 59
def prefixEnd_5773748 : Nat := 4983230072969 + 3 ^ 40 * 5773748 * 2
def baseEnd_5773748 : Nat := 2964707901935581418097023

theorem tailTrace_5773748 : CollatzResearch.WordTrace tailWord_5773748 prefixEnd_5773748 2964707901935581418097023 := by
  unfold tailWord_5773748
  simp only [CollatzResearch.WordTrace]
  refine ⟨105292944943352274248928949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140390593257803032331905265 105292944943352274248928949)
  ·
    refine ⟨9871213588439275710837089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105292944943352274248928949 9871213588439275710837089)
    ·
      refine ⟨7403410191329456783127817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9871213588439275710837089 7403410191329456783127817)
      ·
        refine ⟨5552557643497092587345863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7403410191329456783127817 5552557643497092587345863)
        ·
          refine ⟨8328836465245638881018795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552557643497092587345863 8328836465245638881018795)
          ·
            refine ⟨12493254697868458321528193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328836465245638881018795 12493254697868458321528193)
            ·
              refine ⟨9369941023401343741146145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12493254697868458321528193 9369941023401343741146145)
              ·
                refine ⟨7027455767551007805859609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9369941023401343741146145 7027455767551007805859609)
                ·
                  refine ⟨5270591825663255854394707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027455767551007805859609 5270591825663255854394707)
                  ·
                    refine ⟨7905887738494883781592061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270591825663255854394707 7905887738494883781592061)
                    ·
                      refine ⟨2964707901935581418097023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905887738494883781592061 2964707901935581418097023)
                      ·
                        rfl

theorem cell23_5773748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_5773748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773748 prefixEnd_5773748 := by exact prefixLift 5773748
  have htrace : WordTrace (prefixWord ++ tailWord_5773748) baseStart_5773748 baseEnd_5773748 := by
    simpa [prefixWord, tailWord_5773748, baseEnd_5773748] using wordTrace_append hprefix tailTrace_5773748
  have hstable : (prefixWord ++ tailWord_5773748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773748).length < 2 ^ (prefixWord ++ tailWord_5773748).sum := by decide
  have hdescent : baseEnd_5773748 < baseStart_5773748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773770 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_5773770 : Nat := 118140960795 + 5773770 * 2 ^ 59
def prefixEnd_5773770 : Nat := 4983230072969 + 3 ^ 40 * 5773770 * 2
def baseEnd_5773770 : Nat := 2964719198509980332021921

theorem tailTrace_5773770 : CollatzResearch.WordTrace tailWord_5773770 prefixEnd_5773770 2964719198509980332021921 := by
  unfold tailWord_5773770
  simp only [CollatzResearch.WordTrace]
  refine ⟨52646673073156211563789691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140391128195083230836772509 52646673073156211563789691)
  ·
    refine ⟨78970009609734317345684537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52646673073156211563789691 78970009609734317345684537)
    ·
      refine ⟨59227507207300738009263403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78970009609734317345684537 59227507207300738009263403)
      ·
        refine ⟨88841260810951107013895105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59227507207300738009263403 88841260810951107013895105)
        ·
          refine ⟨66630945608213330260421329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88841260810951107013895105 66630945608213330260421329)
          ·
            refine ⟨49973209206159997695315997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66630945608213330260421329 49973209206159997695315997)
            ·
              refine ⟨18739953452309999135743499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49973209206159997695315997 18739953452309999135743499)
              ·
                refine ⟨28109930178464998703615249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18739953452309999135743499 28109930178464998703615249)
                ·
                  refine ⟨21082447633848749027711437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28109930178464998703615249 21082447633848749027711437)
                  ·
                    refine ⟨7905917862693280885391789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21082447633848749027711437 7905917862693280885391789)
                    ·
                      refine ⟨2964719198509980332021921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7905917862693280885391789 2964719198509980332021921)
                      ·
                        rfl

theorem cell23_5773770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_5773770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773770 prefixEnd_5773770 := by exact prefixLift 5773770
  have htrace : WordTrace (prefixWord ++ tailWord_5773770) baseStart_5773770 baseEnd_5773770 := by
    simpa [prefixWord, tailWord_5773770, baseEnd_5773770] using wordTrace_append hprefix tailTrace_5773770
  have hstable : (prefixWord ++ tailWord_5773770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773770).length < 2 ^ (prefixWord ++ tailWord_5773770).sum := by decide
  have hdescent : baseEnd_5773770 < baseStart_5773770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773823 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_5773823 : Nat := 118140960795 + 5773823 * 2 ^ 59
def prefixEnd_5773823 : Nat := 4983230072969 + 3 ^ 40 * 5773823 * 2
def baseEnd_5773823 : Nat := 2964746412984668624659177

theorem tailTrace_5773823 : CollatzResearch.WordTrace tailWord_5773823 prefixEnd_5773823 2964746412984668624659177 := by
  unfold tailWord_5773823
  simp only [CollatzResearch.WordTrace]
  refine ⟨210588625361432836306838123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140392416907621890871225415 210588625361432836306838123)
  ·
    refine ⟨315882938042149254460257185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210588625361432836306838123 315882938042149254460257185)
    ·
      refine ⟨236912203531611940845192889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315882938042149254460257185 236912203531611940845192889)
      ·
        refine ⟨177684152648708955633894667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236912203531611940845192889 177684152648708955633894667)
        ·
          refine ⟨266526228973063433450842001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177684152648708955633894667 266526228973063433450842001)
          ·
            refine ⟨199894671729797575088131501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266526228973063433450842001 199894671729797575088131501)
            ·
              refine ⟨74960501898674090658049313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199894671729797575088131501 74960501898674090658049313)
              ·
                refine ⟨56220376424005567993536985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74960501898674090658049313 56220376424005567993536985)
                ·
                  refine ⟨42165282318004175995152739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56220376424005567993536985 42165282318004175995152739)
                  ·
                    refine ⟨63247923477006263992729109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42165282318004175995152739 63247923477006263992729109)
                    ·
                      refine ⟨2964746412984668624659177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63247923477006263992729109 2964746412984668624659177)
                      ·
                        rfl

theorem cell23_5773823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_5773823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773823 prefixEnd_5773823 := by exact prefixLift 5773823
  have htrace : WordTrace (prefixWord ++ tailWord_5773823) baseStart_5773823 baseEnd_5773823 := by
    simpa [prefixWord, tailWord_5773823, baseEnd_5773823] using wordTrace_append hprefix tailTrace_5773823
  have hstable : (prefixWord ++ tailWord_5773823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773823).length < 2 ^ (prefixWord ++ tailWord_5773823).sum := by decide
  have hdescent : baseEnd_5773823 < baseStart_5773823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773864 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5773864 : Nat := 118140960795 + 5773864 * 2 ^ 59
def prefixEnd_5773864 : Nat := 4983230072969 + 3 ^ 40 * 5773864 * 2
def baseEnd_5773864 : Nat := 2964767465691502964246489

theorem tailTrace_5773864 : CollatzResearch.WordTrace tailWord_5773864 prefixEnd_5773864 2964767465691502964246489 := by
  unfold tailWord_5773864
  simp only [CollatzResearch.WordTrace]
  refine ⟨105295060377142150154540323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140393413836189533539387097 105295060377142150154540323)
  ·
    refine ⟨157942590565713225231810485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105295060377142150154540323 157942590565713225231810485)
    ·
      refine ⟨14807117865535614865482233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157942590565713225231810485 14807117865535614865482233)
      ·
        refine ⟨11105338399151711149111675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807117865535614865482233 11105338399151711149111675)
        ·
          refine ⟨16658007598727566723667513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105338399151711149111675 16658007598727566723667513)
          ·
            refine ⟨12493505699045675042750635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16658007598727566723667513 12493505699045675042750635)
            ·
              refine ⟨18740258548568512564125953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12493505699045675042750635 18740258548568512564125953)
              ·
                refine ⟨14055193911426384423094465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18740258548568512564125953 14055193911426384423094465)
                ·
                  refine ⟨10541395433569788317320849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14055193911426384423094465 10541395433569788317320849)
                  ·
                    refine ⟨7906046575177341237990637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10541395433569788317320849 7906046575177341237990637)
                    ·
                      refine ⟨2964767465691502964246489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906046575177341237990637 2964767465691502964246489)
                      ·
                        rfl

theorem cell23_5773864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5773864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773864 prefixEnd_5773864 := by exact prefixLift 5773864
  have htrace : WordTrace (prefixWord ++ tailWord_5773864) baseStart_5773864 baseEnd_5773864 := by
    simpa [prefixWord, tailWord_5773864, baseEnd_5773864] using wordTrace_append hprefix tailTrace_5773864
  have hstable : (prefixWord ++ tailWord_5773864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773864).length < 2 ^ (prefixWord ++ tailWord_5773864).sum := by decide
  have hdescent : baseEnd_5773864 < baseStart_5773864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773880 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 3, 5]
def baseStart_5773880 : Nat := 118140960795 + 5773880 * 2 ^ 59
def prefixEnd_5773880 : Nat := 4983230072969 + 3 ^ 40 * 5773880 * 2
def baseEnd_5773880 : Nat := 988258560460658300548805

theorem tailTrace_5773880 : CollatzResearch.WordTrace tailWord_5773880 prefixEnd_5773880 988258560460658300548805 := by
  unfold tailWord_5773880
  simp only [CollatzResearch.WordTrace]
  refine ⟨105295352161113167520831547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140393802881484223361108729 105295352161113167520831547)
  ·
    refine ⟨157943028241669751281247321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105295352161113167520831547 157943028241669751281247321)
    ·
      refine ⟨118457271181252313460935491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157943028241669751281247321 118457271181252313460935491)
      ·
        refine ⟨177685906771878470191403237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118457271181252313460935491 177685906771878470191403237)
        ·
          refine ⟨33316107519727213160888107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177685906771878470191403237 33316107519727213160888107)
          ·
            refine ⟨49974161279590819741332161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33316107519727213160888107 49974161279590819741332161)
            ·
              refine ⟨37480620959693114805999121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49974161279590819741332161 37480620959693114805999121)
              ·
                refine ⟨28110465719769836104499341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37480620959693114805999121 28110465719769836104499341)
                ·
                  refine ⟨10541424644913688539187253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28110465719769836104499341 10541424644913688539187253)
                  ·
                    refine ⟨988258560460658300548805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10541424644913688539187253 988258560460658300548805)
                    ·
                      rfl

theorem cell23_5773880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_5773880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773880 prefixEnd_5773880 := by exact prefixLift 5773880
  have htrace : WordTrace (prefixWord ++ tailWord_5773880) baseStart_5773880 baseEnd_5773880 := by
    simpa [prefixWord, tailWord_5773880, baseEnd_5773880] using wordTrace_append hprefix tailTrace_5773880
  have hstable : (prefixWord ++ tailWord_5773880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773880).length < 2 ^ (prefixWord ++ tailWord_5773880).sum := by decide
  have hdescent : baseEnd_5773880 < baseStart_5773880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773884 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 6]
def baseStart_5773884 : Nat := 118140960795 + 5773884 * 2 ^ 59
def prefixEnd_5773884 : Nat := 4983230072969 + 3 ^ 40 * 5773884 * 2
def baseEnd_5773884 : Nat := 329419748367176987332933

theorem tailTrace_5773884 : CollatzResearch.WordTrace tailWord_5773884 prefixEnd_5773884 329419748367176987332933 := by
  unfold tailWord_5773884
  simp only [CollatzResearch.WordTrace]
  refine ⟨105295425107105921862404353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140393900142807895816539137 105295425107105921862404353)
  ·
    refine ⟨78971568830329441396803265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105295425107105921862404353 78971568830329441396803265)
    ·
      refine ⟨59228676622747081047602449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78971568830329441396803265 59228676622747081047602449)
      ·
        refine ⟨44421507467060310785701837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59228676622747081047602449 44421507467060310785701837)
        ·
          refine ⟨16658065300147616544638189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44421507467060310785701837 16658065300147616544638189)
          ·
            refine ⟨6246774487555356204239321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16658065300147616544638189 6246774487555356204239321)
            ·
              refine ⟨4685080865666517153179491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246774487555356204239321 4685080865666517153179491)
              ·
                refine ⟨7027621298499775729769237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685080865666517153179491 7027621298499775729769237)
                ·
                  refine ⟨329419748367176987332933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7027621298499775729769237 329419748367176987332933)
                  ·
                    rfl

theorem cell23_5773884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_5773884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773884 prefixEnd_5773884 := by exact prefixLift 5773884
  have htrace : WordTrace (prefixWord ++ tailWord_5773884) baseStart_5773884 baseEnd_5773884 := by
    simpa [prefixWord, tailWord_5773884, baseEnd_5773884] using wordTrace_append hprefix tailTrace_5773884
  have hstable : (prefixWord ++ tailWord_5773884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773884).length < 2 ^ (prefixWord ++ tailWord_5773884).sum := by decide
  have hdescent : baseEnd_5773884 < baseStart_5773884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773887 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 4, 3, 2]
def baseStart_5773887 : Nat := 118140960795 + 5773887 * 2 ^ 59
def prefixEnd_5773887 : Nat := 4983230072969 + 3 ^ 40 * 5773887 * 2
def baseEnd_5773887 : Nat := 2964779275746556374258883

theorem tailTrace_5773887 : CollatzResearch.WordTrace tailWord_5773887 prefixEnd_5773887 2964779275746556374258883 := by
  unfold tailWord_5773887
  simp only [CollatzResearch.WordTrace]
  refine ⟨210590959633200975237167915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140393973088800650158111943 210590959633200975237167915)
  ·
    refine ⟨315886439449801462855751873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210590959633200975237167915 315886439449801462855751873)
    ·
      refine ⟨236914829587351097141813905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315886439449801462855751873 236914829587351097141813905)
      ·
        refine ⟨177686122190513322856360429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236914829587351097141813905 177686122190513322856360429)
        ·
          refine ⟨66632295821442496071135161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177686122190513322856360429 66632295821442496071135161)
          ·
            refine ⟨49974221866081872053351371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66632295821442496071135161 49974221866081872053351371)
            ·
              refine ⟨74961332799122808080027057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49974221866081872053351371 74961332799122808080027057)
              ·
                refine ⟨56220999599342106060020293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74961332799122808080027057 56220999599342106060020293)
                ·
                  refine ⟨10541437424876644886253805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56220999599342106060020293 10541437424876644886253805)
                  ·
                    refine ⟨3953039034328741832345177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10541437424876644886253805 3953039034328741832345177)
                    ·
                      refine ⟨2964779275746556374258883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953039034328741832345177 2964779275746556374258883)
                      ·
                        rfl

theorem cell23_5773887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_5773887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773887 prefixEnd_5773887 := by exact prefixLift 5773887
  have htrace : WordTrace (prefixWord ++ tailWord_5773887) baseStart_5773887 baseEnd_5773887 := by
    simpa [prefixWord, tailWord_5773887, baseEnd_5773887] using wordTrace_append hprefix tailTrace_5773887
  have hstable : (prefixWord ++ tailWord_5773887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773887).length < 2 ^ (prefixWord ++ tailWord_5773887).sum := by decide
  have hdescent : baseEnd_5773887 < baseStart_5773887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773918 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5773918 : Nat := 118140960795 + 5773918 * 2 ^ 59
def prefixEnd_5773918 : Nat := 4983230072969 + 3 ^ 40 * 5773918 * 2
def baseEnd_5773918 : Nat := 329421688182982861441249

theorem tailTrace_5773918 : CollatzResearch.WordTrace tailWord_5773918 prefixEnd_5773918 329421688182982861441249 := by
  unfold tailWord_5773918
  simp only [CollatzResearch.WordTrace]
  refine ⟨26324011287011083441443301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140394726864059111687697605 26324011287011083441443301)
  ·
    refine ⟨4935752116314578145270619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26324011287011083441443301 4935752116314578145270619)
    ·
      refine ⟨7403628174471867217905929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935752116314578145270619 7403628174471867217905929)
      ·
        refine ⟨5552721130853900413429447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7403628174471867217905929 5552721130853900413429447)
        ·
          refine ⟨8329081696280850620144171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552721130853900413429447 8329081696280850620144171)
          ·
            refine ⟨12493622544421275930216257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329081696280850620144171 12493622544421275930216257)
            ·
              refine ⟨9370216908315956947662193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12493622544421275930216257 9370216908315956947662193)
              ·
                refine ⟨7027662681236967710746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9370216908315956947662193 7027662681236967710746645)
                ·
                  refine ⟨329421688182982861441249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7027662681236967710746645 329421688182982861441249)
                  ·
                    rfl

theorem cell23_5773918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5773918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773918 prefixEnd_5773918 := by exact prefixLift 5773918
  have htrace : WordTrace (prefixWord ++ tailWord_5773918) baseStart_5773918 baseEnd_5773918 := by
    simpa [prefixWord, tailWord_5773918, baseEnd_5773918] using wordTrace_append hprefix tailTrace_5773918
  have hstable : (prefixWord ++ tailWord_5773918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773918).length < 2 ^ (prefixWord ++ tailWord_5773918).sum := by decide
  have hdescent : baseEnd_5773918 < baseStart_5773918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773922 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5773922 : Nat := 118140960795 + 5773922 * 2 ^ 59
def prefixEnd_5773922 : Nat := 4983230072969 + 3 ^ 40 * 5773922 * 2
def baseEnd_5773922 : Nat := 988265749189821245773741

theorem tailTrace_5773922 : CollatzResearch.WordTrace tailWord_5773922 prefixEnd_5773922 988265749189821245773741 := by
  unfold tailWord_5773922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52648059047018544053673005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140394824125382784143128013 52648059047018544053673005)
  ·
    refine ⟨19743022142631954020127377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52648059047018544053673005 19743022142631954020127377)
    ·
      refine ⟨14807266606973965515095533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19743022142631954020127377 14807266606973965515095533)
      ·
        refine ⟨5552724977615237068160825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14807266606973965515095533 5552724977615237068160825)
        ·
          refine ⟨4164543733211427801120619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552724977615237068160825 4164543733211427801120619)
          ·
            refine ⟨6246815599817141701680929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164543733211427801120619 6246815599817141701680929)
            ·
              refine ⟨4685111699862856276260697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246815599817141701680929 4685111699862856276260697)
              ·
                refine ⟨3513833774897142207195523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685111699862856276260697 3513833774897142207195523)
                ·
                  refine ⟨5270750662345713310793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513833774897142207195523 5270750662345713310793285)
                  ·
                    refine ⟨988265749189821245773741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270750662345713310793285 988265749189821245773741)
                    ·
                      rfl

theorem cell23_5773922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5773922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773922 prefixEnd_5773922 := by exact prefixLift 5773922
  have htrace : WordTrace (prefixWord ++ tailWord_5773922) baseStart_5773922 baseEnd_5773922 := by
    simpa [prefixWord, tailWord_5773922, baseEnd_5773922] using wordTrace_append hprefix tailTrace_5773922
  have hstable : (prefixWord ++ tailWord_5773922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773922).length < 2 ^ (prefixWord ++ tailWord_5773922).sum := by decide
  have hdescent : baseEnd_5773922 < baseStart_5773922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773928 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5773928 : Nat := 118140960795 + 5773928 * 2 ^ 59
def prefixEnd_5773928 : Nat := 4983230072969 + 3 ^ 40 * 5773928 * 2
def baseEnd_5773928 : Nat := 2964800328453390713846195

theorem tailTrace_5773928 : CollatzResearch.WordTrace tailWord_5773928 prefixEnd_5773928 2964800328453390713846195 := by
  unfold tailWord_5773928
  simp only [CollatzResearch.WordTrace]
  refine ⟨105296227513026219619705219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140394970017368292826273625 105296227513026219619705219)
  ·
    refine ⟨157944341269539329429557829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105296227513026219619705219 157944341269539329429557829)
    ·
      refine ⟨29614563988038624268042093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 157944341269539329429557829 29614563988038624268042093)
      ·
        refine ⟨11105461495514484100515785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29614563988038624268042093 11105461495514484100515785)
        ·
          refine ⟨8329096121635863075386839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11105461495514484100515785 8329096121635863075386839)
          ·
            refine ⟨12493644182453794613080259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329096121635863075386839 12493644182453794613080259)
            ·
              refine ⟨18740466273680691919620389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12493644182453794613080259 18740466273680691919620389)
              ·
                refine ⟨3513837426315129734928823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18740466273680691919620389 3513837426315129734928823)
                ·
                  refine ⟨5270756139472694602393235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513837426315129734928823 5270756139472694602393235)
                  ·
                    refine ⟨7906134209209041903589853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270756139472694602393235 7906134209209041903589853)
                    ·
                      refine ⟨2964800328453390713846195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906134209209041903589853 2964800328453390713846195)
                      ·
                        rfl

theorem cell23_5773928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5773928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773928 prefixEnd_5773928 := by exact prefixLift 5773928
  have htrace : WordTrace (prefixWord ++ tailWord_5773928) baseStart_5773928 baseEnd_5773928 := by
    simpa [prefixWord, tailWord_5773928, baseEnd_5773928] using wordTrace_append hprefix tailTrace_5773928
  have hstable : (prefixWord ++ tailWord_5773928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773928).length < 2 ^ (prefixWord ++ tailWord_5773928).sum := by decide
  have hdescent : baseEnd_5773928 < baseStart_5773928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773957 : List Nat := [1, 3, 1, 1, 4, 3, 3, 7]
def baseStart_5773957 : Nat := 118140960795 + 5773957 * 2 ^ 59
def prefixEnd_5773957 : Nat := 4983230072969 + 3 ^ 40 * 5773957 * 2
def baseEnd_5773957 : Nat := 109807971088606337051243

theorem tailTrace_5773957 : CollatzResearch.WordTrace tailWord_5773957 prefixEnd_5773957 109807971088606337051243 := by
  unfold tailWord_5773957
  simp only [CollatzResearch.WordTrace]
  refine ⟨210593512742947377192216125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140395675161964918128144083 210593512742947377192216125)
  ·
    refine ⟨78972567278605266447081047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210593512742947377192216125 78972567278605266447081047)
    ·
      refine ⟨118458850917907899670621571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78972567278605266447081047 118458850917907899670621571)
      ·
        refine ⟨177688276376861849505932357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118458850917907899670621571 177688276376861849505932357)
        ·
          refine ⟨33316551820661596782362317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177688276376861849505932357 33316551820661596782362317)
          ·
            refine ⟨12493706932748098793385869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33316551820661596782362317 12493706932748098793385869)
            ·
              refine ⟨4685140099780537047519701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12493706932748098793385869 4685140099780537047519701)
              ·
                refine ⟨109807971088606337051243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4685140099780537047519701 109807971088606337051243)
                ·
                  rfl

theorem cell23_5773957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 7].length) (baseStart_5773957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773957 prefixEnd_5773957 := by exact prefixLift 5773957
  have htrace : WordTrace (prefixWord ++ tailWord_5773957) baseStart_5773957 baseEnd_5773957 := by
    simpa [prefixWord, tailWord_5773957, baseEnd_5773957] using wordTrace_append hprefix tailTrace_5773957
  have hstable : (prefixWord ++ tailWord_5773957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773957).length < 2 ^ (prefixWord ++ tailWord_5773957).sum := by decide
  have hdescent : baseEnd_5773957 < baseStart_5773957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773967 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_5773967 : Nat := 118140960795 + 5773967 * 2 ^ 59
def prefixEnd_5773967 : Nat := 4983230072969 + 3 ^ 40 * 5773967 * 2
def baseEnd_5773967 : Nat := 2964820354198916061258515

theorem tailTrace_5773967 : CollatzResearch.WordTrace tailWord_5773967 prefixEnd_5773967 2964820354198916061258515 := by
  unfold tailWord_5773967
  simp only [CollatzResearch.WordTrace]
  refine ⟨210593877472911148900080155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140395918315274099266720103 210593877472911148900080155)
  ·
    refine ⟨315890816209366723350120233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210593877472911148900080155 315890816209366723350120233)
    ·
      refine ⟨236918112157025042512590175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315890816209366723350120233 236918112157025042512590175)
      ·
        refine ⟨355377168235537563768885263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236918112157025042512590175 355377168235537563768885263)
        ·
          refine ⟨533065752353306345653327895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355377168235537563768885263 533065752353306345653327895)
          ·
            refine ⟨799598628529959518479991843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533065752353306345653327895 799598628529959518479991843)
            ·
              refine ⟨1199397942794939277719987765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799598628529959518479991843 1199397942794939277719987765)
              ·
                refine ⟨112443557137025557286248853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199397942794939277719987765 112443557137025557286248853)
                ·
                  refine ⟨5270791740798072997792915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112443557137025557286248853 5270791740798072997792915)
                  ·
                    refine ⟨7906187611197109496689373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270791740798072997792915 7906187611197109496689373)
                    ·
                      refine ⟨2964820354198916061258515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906187611197109496689373 2964820354198916061258515)
                      ·
                        rfl

theorem cell23_5773967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_5773967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773967 prefixEnd_5773967 := by exact prefixLift 5773967
  have htrace : WordTrace (prefixWord ++ tailWord_5773967) baseStart_5773967 baseEnd_5773967 := by
    simpa [prefixWord, tailWord_5773967, baseEnd_5773967] using wordTrace_append hprefix tailTrace_5773967
  have hstable : (prefixWord ++ tailWord_5773967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773967).length < 2 ^ (prefixWord ++ tailWord_5773967).sum := by decide
  have hdescent : baseEnd_5773967 < baseStart_5773967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5773978 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_5773978 : Nat := 118140960795 + 5773978 * 2 ^ 59
def prefixEnd_5773978 : Nat := 4983230072969 + 3 ^ 40 * 5773978 * 2
def baseEnd_5773978 : Nat := 988275334162038506073655

theorem tailTrace_5773978 : CollatzResearch.WordTrace tailWord_5773978 prefixEnd_5773978 988275334162038506073655 := by
  unfold tailWord_5773978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52648569668967824444682647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140396185783914198519153725 52648569668967824444682647)
  ·
    refine ⟨78972854503451736667023971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52648569668967824444682647 78972854503451736667023971)
    ·
      refine ⟨118459281755177605000535957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78972854503451736667023971 118459281755177605000535957)
      ·
        refine ⟨5552778832273950234400123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118459281755177605000535957 5552778832273950234400123)
        ·
          refine ⟨8329168248410925351600185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552778832273950234400123 8329168248410925351600185)
          ·
            refine ⟨6246876186308194013700139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8329168248410925351600185 6246876186308194013700139)
            ·
              refine ⟨9370314279462291020550209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246876186308194013700139 9370314279462291020550209)
              ·
                refine ⟨7027735709596718265412657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9370314279462291020550209 7027735709596718265412657)
                ·
                  refine ⟨5270801782197538699059493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027735709596718265412657 5270801782197538699059493)
                  ·
                    refine ⟨988275334162038506073655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270801782197538699059493 988275334162038506073655)
                    ·
                      rfl

theorem cell23_5773978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_5773978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5773978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5773978 prefixEnd_5773978 := by exact prefixLift 5773978
  have htrace : WordTrace (prefixWord ++ tailWord_5773978) baseStart_5773978 baseEnd_5773978 := by
    simpa [prefixWord, tailWord_5773978, baseEnd_5773978] using wordTrace_append hprefix tailTrace_5773978
  have hstable : (prefixWord ++ tailWord_5773978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5773978).length < 2 ^ (prefixWord ++ tailWord_5773978).sum := by decide
  have hdescent : baseEnd_5773978 < baseStart_5773978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5773978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774041 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 2, 2, 2]
def baseStart_5774041 : Nat := 118140960795 + 5774041 * 2 ^ 59
def prefixEnd_5774041 : Nat := 4983230072969 + 3 ^ 40 * 5774041 * 2
def baseEnd_5774041 : Nat := 2964858351767348771733175

theorem tailTrace_5774041 : CollatzResearch.WordTrace tailWord_5774041 prefixEnd_5774041 2964858351767348771733175 := by
  unfold tailWord_5774041
  simp only [CollatzResearch.WordTrace]
  refine ⟨210596576474643059538273977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140397717649762039692182651 210596576474643059538273977)
  ·
    refine ⟨157947432355982294653705483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210596576474643059538273977 157947432355982294653705483)
    ·
      refine ⟨236921148533973441980558225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157947432355982294653705483 236921148533973441980558225)
      ·
        refine ⟨177690861400480081485418669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236921148533973441980558225 177690861400480081485418669)
        ·
          refine ⟨66634073025180030557032001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177690861400480081485418669 66634073025180030557032001)
          ·
            refine ⟨49975554768885022917774001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66634073025180030557032001 49975554768885022917774001)
            ·
              refine ⟨37481666076663767188330501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49975554768885022917774001 37481666076663767188330501)
              ·
                refine ⟨7027812389374456347811969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37481666076663767188330501 7027812389374456347811969)
                ·
                  refine ⟨5270859292030842260858977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027812389374456347811969 5270859292030842260858977)
                  ·
                    refine ⟨3953144469023131695644233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5270859292030842260858977 3953144469023131695644233)
                    ·
                      refine ⟨2964858351767348771733175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953144469023131695644233 2964858351767348771733175)
                      ·
                        rfl

theorem cell23_5774041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_5774041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774041 prefixEnd_5774041 := by exact prefixLift 5774041
  have htrace : WordTrace (prefixWord ++ tailWord_5774041) baseStart_5774041 baseEnd_5774041 := by
    simpa [prefixWord, tailWord_5774041, baseEnd_5774041] using wordTrace_append hprefix tailTrace_5774041
  have hstable : (prefixWord ++ tailWord_5774041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774041).length < 2 ^ (prefixWord ++ tailWord_5774041).sum := by decide
  have hdescent : baseEnd_5774041 < baseStart_5774041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774047 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 7]
def baseStart_5774047 : Nat := 118140960795 + 5774047 * 2 ^ 59
def prefixEnd_5774047 : Nat := 4983230072969 + 3 ^ 40 * 5774047 * 2
def baseEnd_5774047 : Nat := 329429048072363972028683

theorem tailTrace_5774047 : CollatzResearch.WordTrace tailWord_5774047 prefixEnd_5774047 329429048072363972028683 := by
  unfold tailWord_5774047
  simp only [CollatzResearch.WordTrace]
  refine ⟨210596795312621322562992395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140397863541747548375328263 210596795312621322562992395)
  ·
    refine ⟨315895192968931983844488593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210596795312621322562992395 315895192968931983844488593)
    ·
      refine ⟨236921394726698987883366445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315895192968931983844488593 236921394726698987883366445)
      ·
        refine ⟨88845523022512120456262417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236921394726698987883366445 88845523022512120456262417)
        ·
          refine ⟨66634142266884090342196813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88845523022512120456262417 66634142266884090342196813)
          ·
            refine ⟨24987803350081533878323805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66634142266884090342196813 24987803350081533878323805)
            ·
              refine ⟨9370426256280575204371427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24987803350081533878323805 9370426256280575204371427)
              ·
                refine ⟨14055639384420862806557141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9370426256280575204371427 14055639384420862806557141)
                ·
                  refine ⟨329429048072363972028683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14055639384420862806557141 329429048072363972028683)
                  ·
                    rfl

theorem cell23_5774047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 7].length) (baseStart_5774047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774047 prefixEnd_5774047 := by exact prefixLift 5774047
  have htrace : WordTrace (prefixWord ++ tailWord_5774047) baseStart_5774047 baseEnd_5774047 := by
    simpa [prefixWord, tailWord_5774047, baseEnd_5774047] using wordTrace_append hprefix tailTrace_5774047
  have hstable : (prefixWord ++ tailWord_5774047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774047).length < 2 ^ (prefixWord ++ tailWord_5774047).sum := by decide
  have hdescent : baseEnd_5774047 < baseStart_5774047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774057 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_5774057 : Nat := 118140960795 + 5774057 * 2 ^ 59
def prefixEnd_5774057 : Nat := 4983230072969 + 3 ^ 40 * 5774057 * 2
def baseEnd_5774057 : Nat := 2964866567457820709133101

theorem tailTrace_5774057 : CollatzResearch.WordTrace tailWord_5774057 prefixEnd_5774057 2964866567457820709133101 := by
  unfold tailWord_5774057
  simp only [CollatzResearch.WordTrace]
  refine ⟨210597160042585094270856425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140398106695056729513904283 210597160042585094270856425)
  ·
    refine ⟨157947870031938820703142319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210597160042585094270856425 157947870031938820703142319)
    ·
      refine ⟨236921805047908231054713479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157947870031938820703142319 236921805047908231054713479)
      ·
        refine ⟨355382707571862346582070219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236921805047908231054713479 355382707571862346582070219)
        ·
          refine ⟨533074061357793519873105329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355382707571862346582070219 533074061357793519873105329)
          ·
            refine ⟨399805546018345139904828997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533074061357793519873105329 399805546018345139904828997)
            ·
              refine ⟨74963539878439713732155437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399805546018345139904828997 74963539878439713732155437)
              ·
                refine ⟨28111327454414892649558289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74963539878439713732155437 28111327454414892649558289)
                ·
                  refine ⟨21083495590811169487168717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28111327454414892649558289 21083495590811169487168717)
                  ·
                    refine ⟨7906310846554188557688269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21083495590811169487168717 7906310846554188557688269)
                    ·
                      refine ⟨2964866567457820709133101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906310846554188557688269 2964866567457820709133101)
                      ·
                        rfl

theorem cell23_5774057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_5774057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774057 prefixEnd_5774057 := by exact prefixLift 5774057
  have htrace : WordTrace (prefixWord ++ tailWord_5774057) baseStart_5774057 baseEnd_5774057 := by
    simpa [prefixWord, tailWord_5774057, baseEnd_5774057] using wordTrace_append hprefix tailTrace_5774057
  have hstable : (prefixWord ++ tailWord_5774057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774057).length < 2 ^ (prefixWord ++ tailWord_5774057).sum := by decide
  have hdescent : baseEnd_5774057 < baseStart_5774057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774098 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_5774098 : Nat := 118140960795 + 5774098 * 2 ^ 59
def prefixEnd_5774098 : Nat := 4983230072969 + 3 ^ 40 * 5774098 * 2
def baseEnd_5774098 : Nat := 329431957796072783191157

theorem tailTrace_5774098 : CollatzResearch.WordTrace tailWord_5774098 prefixEnd_5774098 329431957796072783191157 := by
  unfold tailWord_5774098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52649663858859139568274737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140399103623624372182065965 52649663858859139568274737)
  ·
    refine ⟨39487247894144354676206053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52649663858859139568274737 39487247894144354676206053)
    ·
      refine ⟨7403858980152066501788635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39487247894144354676206053 7403858980152066501788635)
      ·
        refine ⟨11105788470228099752682953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403858980152066501788635 11105788470228099752682953)
        ·
          refine ⟨8329341352671074814512215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11105788470228099752682953 8329341352671074814512215)
          ·
            refine ⟨12494012029006612221768323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329341352671074814512215 12494012029006612221768323)
            ·
              refine ⟨18741018043509918332652485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12494012029006612221768323 18741018043509918332652485)
              ·
                refine ⟨3513940883158109687372341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18741018043509918332652485 3513940883158109687372341)
                ·
                  refine ⟨329431957796072783191157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513940883158109687372341 329431957796072783191157)
                  ·
                    rfl

theorem cell23_5774098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_5774098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774098 prefixEnd_5774098 := by exact prefixLift 5774098
  have htrace : WordTrace (prefixWord ++ tailWord_5774098) baseStart_5774098 baseEnd_5774098 := by
    simpa [prefixWord, tailWord_5774098, baseEnd_5774098] using wordTrace_append hprefix tailTrace_5774098
  have hstable : (prefixWord ++ tailWord_5774098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774098).length < 2 ^ (prefixWord ++ tailWord_5774098).sum := by decide
  have hdescent : baseEnd_5774098 < baseStart_5774098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774124 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_5774124 : Nat := 118140960795 + 5774124 * 2 ^ 59
def prefixEnd_5774124 : Nat := 4983230072969 + 3 ^ 40 * 5774124 * 2
def baseEnd_5774124 : Nat := 988300323553890648998431

theorem tailTrace_5774124 : CollatzResearch.WordTrace tailWord_5774124 prefixEnd_5774124 988300323553890648998431 := by
  unfold tailWord_5774124
  simp only [CollatzResearch.WordTrace]
  refine ⟨105299801866671182356772713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140399735822228243142363617 105299801866671182356772713)
  ·
    refine ⟨78974851400003386767579535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105299801866671182356772713 78974851400003386767579535)
    ·
      refine ⟨118462277100005080151369303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78974851400003386767579535 118462277100005080151369303)
      ·
        refine ⟨177693415650007620227053955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118462277100005080151369303 177693415650007620227053955)
        ·
          refine ⟨266540123475011430340580933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177693415650007620227053955 266540123475011430340580933)
          ·
            refine ⟨49976273151564643188858925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266540123475011430340580933 49976273151564643188858925)
            ·
              refine ⟨18741102431836741195822097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49976273151564643188858925 18741102431836741195822097)
              ·
                refine ⟨14055826823877555896866573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18741102431836741195822097 14055826823877555896866573)
                ·
                  refine ⟨5270935058954083461324965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14055826823877555896866573 5270935058954083461324965)
                  ·
                    refine ⟨988300323553890648998431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270935058954083461324965 988300323553890648998431)
                    ·
                      rfl

theorem cell23_5774124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_5774124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774124 prefixEnd_5774124 := by exact prefixLift 5774124
  have htrace : WordTrace (prefixWord ++ tailWord_5774124) baseStart_5774124 baseEnd_5774124 := by
    simpa [prefixWord, tailWord_5774124, baseEnd_5774124] using wordTrace_append hprefix tailTrace_5774124
  have hstable : (prefixWord ++ tailWord_5774124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774124).length < 2 ^ (prefixWord ++ tailWord_5774124).sum := by decide
  have hdescent : baseEnd_5774124 < baseStart_5774124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774131 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 4]
def baseStart_5774131 : Nat := 118140960795 + 5774131 * 2 ^ 59
def prefixEnd_5774131 : Nat := 4983230072969 + 3 ^ 40 * 5774131 * 2
def baseEnd_5774131 : Nat := 2964904565026253419607761

theorem tailTrace_5774131 : CollatzResearch.WordTrace tailWord_5774131 prefixEnd_5774131 2964904565026253419607761 := by
  unfold tailWord_5774131
  simp only [CollatzResearch.WordTrace]
  refine ⟨210599859044317004909050247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140399906029544669939366831 210599859044317004909050247)
  ·
    refine ⟨315899788566475507363575371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210599859044317004909050247 315899788566475507363575371)
    ·
      refine ⟨473849682849713261045363057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315899788566475507363575371 473849682849713261045363057)
      ·
        refine ⟨355387262137284945784022293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473849682849713261045363057 355387262137284945784022293)
        ·
          refine ⟨16658777912685231833626045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 355387262137284945784022293 16658777912685231833626045)
          ·
            refine ⟨6247041717256961937609767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16658777912685231833626045 6247041717256961937609767)
            ·
              refine ⟨9370562575885442906414651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247041717256961937609767 9370562575885442906414651)
              ·
                refine ⟨14055843863828164359621977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9370562575885442906414651 14055843863828164359621977)
                ·
                  refine ⟨10541882897871123269716483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14055843863828164359621977 10541882897871123269716483)
                  ·
                    refine ⟨15812824346806684904574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10541882897871123269716483 15812824346806684904574725)
                    ·
                      refine ⟨2964904565026253419607761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15812824346806684904574725 2964904565026253419607761)
                      ·
                        rfl

theorem cell23_5774131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_5774131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774131 prefixEnd_5774131 := by exact prefixLift 5774131
  have htrace : WordTrace (prefixWord ++ tailWord_5774131) baseStart_5774131 baseEnd_5774131 := by
    simpa [prefixWord, tailWord_5774131, baseEnd_5774131] using wordTrace_append hprefix tailTrace_5774131
  have hstable : (prefixWord ++ tailWord_5774131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774131).length < 2 ^ (prefixWord ++ tailWord_5774131).sum := by decide
  have hdescent : baseEnd_5774131 < baseStart_5774131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774181 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_5774181 : Nat := 118140960795 + 5774181 * 2 ^ 59
def prefixEnd_5774181 : Nat := 4983230072969 + 3 ^ 40 * 5774181 * 2
def baseEnd_5774181 : Nat := 2964930239058978223982531

theorem tailTrace_5774181 : CollatzResearch.WordTrace tailWord_5774181 prefixEnd_5774181 2964930239058978223982531 := by
  unfold tailWord_5774181
  simp only [CollatzResearch.WordTrace]
  refine ⟨210601682694135863448370397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140401121796090575632246931 210601682694135863448370397)
  ·
    refine ⟨78975631010300948793138899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210601682694135863448370397 78975631010300948793138899)
    ·
      refine ⟨118463446515451423189708349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78975631010300948793138899 118463446515451423189708349)
      ·
        refine ⟨44423792443294283696140631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118463446515451423189708349 44423792443294283696140631)
        ·
          refine ⟨66635688664941425544210947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44423792443294283696140631 66635688664941425544210947)
          ·
            refine ⟨99953532997412138316316421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66635688664941425544210947 99953532997412138316316421)
            ·
              refine ⟨18741287437014775934309329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99953532997412138316316421 18741287437014775934309329)
              ·
                refine ⟨14055965577761081950731997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18741287437014775934309329 14055965577761081950731997)
                ·
                  refine ⟨5270987091660405731524499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14055965577761081950731997 5270987091660405731524499)
                  ·
                    refine ⟨7906480637490608597286749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5270987091660405731524499 7906480637490608597286749)
                    ·
                      refine ⟨2964930239058978223982531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906480637490608597286749 2964930239058978223982531)
                      ·
                        rfl

theorem cell23_5774181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_5774181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774181 prefixEnd_5774181 := by exact prefixLift 5774181
  have htrace : WordTrace (prefixWord ++ tailWord_5774181) baseStart_5774181 baseEnd_5774181 := by
    simpa [prefixWord, tailWord_5774181, baseEnd_5774181] using wordTrace_append hprefix tailTrace_5774181
  have hstable : (prefixWord ++ tailWord_5774181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774181).length < 2 ^ (prefixWord ++ tailWord_5774181).sum := by decide
  have hdescent : baseEnd_5774181 < baseStart_5774181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774231 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 2, 4]
def baseStart_5774231 : Nat := 118140960795 + 5774231 * 2 ^ 59
def prefixEnd_5774231 : Nat := 4983230072969 + 3 ^ 40 * 5774231 * 2
def baseEnd_5774231 : Nat := 988318637697234342785767

theorem tailTrace_5774231 : CollatzResearch.WordTrace tailWord_5774231 prefixEnd_5774231 988318637697234342785767 := by
  unfold tailWord_5774231
  simp only [CollatzResearch.WordTrace]
  refine ⟨210603506343954721987690547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140402337562636481325127031 210603506343954721987690547)
  ·
    refine ⟨315905259515932082981535821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210603506343954721987690547 315905259515932082981535821)
    ·
      refine ⟨118464472318474531118075933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315905259515932082981535821 118464472318474531118075933)
      ·
        refine ⟨44424177119427949169278475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118464472318474531118075933 44424177119427949169278475)
        ·
          refine ⟨66636265679141923753917713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44424177119427949169278475 66636265679141923753917713)
          ·
            refine ⟨49977199259356442815438285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66636265679141923753917713 49977199259356442815438285)
            ·
              refine ⟨18741449722258666055789357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49977199259356442815438285 18741449722258666055789357)
              ·
                refine ⟨7028043645846999770921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18741449722258666055789357 7028043645846999770921009)
                ·
                  refine ⟨5271032734385249828190757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7028043645846999770921009 5271032734385249828190757)
                  ·
                    refine ⟨988318637697234342785767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271032734385249828190757 988318637697234342785767)
                    ·
                      rfl

theorem cell23_5774231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_5774231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774231 prefixEnd_5774231 := by exact prefixLift 5774231
  have htrace : WordTrace (prefixWord ++ tailWord_5774231) baseStart_5774231 baseEnd_5774231 := by
    simpa [prefixWord, tailWord_5774231, baseEnd_5774231] using wordTrace_append hprefix tailTrace_5774231
  have hstable : (prefixWord ++ tailWord_5774231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774231).length < 2 ^ (prefixWord ++ tailWord_5774231).sum := by decide
  have hdescent : baseEnd_5774231 < baseStart_5774231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774272 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 1, 2, 2]
def baseStart_5774272 : Nat := 118140960795 + 5774272 * 2 ^ 59
def prefixEnd_5774272 : Nat := 4983230072969 + 3 ^ 40 * 5774272 * 2
def baseEnd_5774272 : Nat := 2964976965798537367944613

theorem tailTrace_5774272 : CollatzResearch.WordTrace tailWord_5774272 prefixEnd_5774272 2964976965798537367944613 := by
  unfold tailWord_5774272
  simp only [CollatzResearch.WordTrace]
  refine ⟨105302500868403092994966535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140403334491204123993288713 105302500868403092994966535)
  ·
    refine ⟨157953751302604639492449803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105302500868403092994966535 157953751302604639492449803)
    ·
      refine ⟨236930626953906959238674705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157953751302604639492449803 236930626953906959238674705)
      ·
        refine ⟨177697970215430219429006029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236930626953906959238674705 177697970215430219429006029)
        ·
          refine ⟨66636738830786332285877261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177697970215430219429006029 66636738830786332285877261)
          ·
            refine ⟨24988777061544874607203973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66636738830786332285877261 24988777061544874607203973)
            ·
              refine ⟨4685395699039663988850745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24988777061544874607203973 4685395699039663988850745)
              ·
                refine ⟨3514046774279747991638059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685395699039663988850745 3514046774279747991638059)
                ·
                  refine ⟨5271070161419621987457089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514046774279747991638059 5271070161419621987457089)
                  ·
                    refine ⟨3953302621064716490592817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5271070161419621987457089 3953302621064716490592817)
                    ·
                      refine ⟨2964976965798537367944613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953302621064716490592817 2964976965798537367944613)
                      ·
                        rfl

theorem cell23_5774272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 2, 2].length) (baseStart_5774272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774272 prefixEnd_5774272 := by exact prefixLift 5774272
  have htrace : WordTrace (prefixWord ++ tailWord_5774272) baseStart_5774272 baseEnd_5774272 := by
    simpa [prefixWord, tailWord_5774272, baseEnd_5774272] using wordTrace_append hprefix tailTrace_5774272
  have hstable : (prefixWord ++ tailWord_5774272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774272).length < 2 ^ (prefixWord ++ tailWord_5774272).sum := by decide
  have hdescent : baseEnd_5774272 < baseStart_5774272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774298 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_5774298 : Nat := 118140960795 + 5774298 * 2 ^ 59
def prefixEnd_5774298 : Nat := 4983230072969 + 3 ^ 40 * 5774298 * 2
def baseEnd_5774298 : Nat := 2964990316295554266219493

theorem tailTrace_5774298 : CollatzResearch.WordTrace tailWord_5774298 prefixEnd_5774298 2964990316295554266219493 := by
  unfold tailWord_5774298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52651487508677998107594887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140403966689807994953586365 52651487508677998107594887)
  ·
    refine ⟨78977231263016997161392331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52651487508677998107594887 78977231263016997161392331)
    ·
      refine ⟨118465846894525495742088497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78977231263016997161392331 118465846894525495742088497)
      ·
        refine ⟨88849385170894121806566373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118465846894525495742088497 88849385170894121806566373)
        ·
          refine ⟨16659259719542647838731195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88849385170894121806566373 16659259719542647838731195)
          ·
            refine ⟨24988889579313971758096793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16659259719542647838731195 24988889579313971758096793)
            ·
              refine ⟨18741667184485478818572595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24988889579313971758096793 18741667184485478818572595)
              ·
                refine ⟨28112500776728218227858893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18741667184485478818572595 28112500776728218227858893)
                ·
                  refine ⟨10542187791273081835447085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28112500776728218227858893 10542187791273081835447085)
                  ·
                    refine ⟨3953320421727405688292657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10542187791273081835447085 3953320421727405688292657)
                    ·
                      refine ⟨2964990316295554266219493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953320421727405688292657 2964990316295554266219493)
                      ·
                        rfl

theorem cell23_5774298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_5774298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774298 prefixEnd_5774298 := by exact prefixLift 5774298
  have htrace : WordTrace (prefixWord ++ tailWord_5774298) baseStart_5774298 baseEnd_5774298 := by
    simpa [prefixWord, tailWord_5774298, baseEnd_5774298] using wordTrace_append hprefix tailTrace_5774298
  have hstable : (prefixWord ++ tailWord_5774298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774298).length < 2 ^ (prefixWord ++ tailWord_5774298).sum := by decide
  have hdescent : baseEnd_5774298 < baseStart_5774298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774309 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5774309 : Nat := 118140960795 + 5774309 * 2 ^ 59
def prefixEnd_5774309 : Nat := 4983230072969 + 3 ^ 40 * 5774309 * 2
def baseEnd_5774309 : Nat := 2964995964582753723181943

theorem tailTrace_5774309 : CollatzResearch.WordTrace tailWord_5774309 prefixEnd_5774309 2964995964582753723181943 := by
  unfold tailWord_5774309
  simp only [CollatzResearch.WordTrace]
  refine ⟨210606351237672141309029981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140404234158448094206019987 210606351237672141309029981)
  ·
    refine ⟨78977381714127052990886243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210606351237672141309029981 78977381714127052990886243)
    ·
      refine ⟨118466072571190579486329365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78977381714127052990886243 118466072571190579486329365)
      ·
        refine ⟨5553097151774558413421689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118466072571190579486329365 5553097151774558413421689)
        ·
          refine ⟨4164822863830918810066267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5553097151774558413421689 4164822863830918810066267)
          ·
            refine ⟨6247234295746378215099401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164822863830918810066267 6247234295746378215099401)
            ·
              refine ⟨4685425721809783661324551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247234295746378215099401 4685425721809783661324551)
              ·
                refine ⟨7028138582714675491986827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685425721809783661324551 7028138582714675491986827)
                ·
                  refine ⟨10542207874072013237980241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028138582714675491986827 10542207874072013237980241)
                  ·
                    refine ⟨7906655905554009928485181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10542207874072013237980241 7906655905554009928485181)
                    ·
                      refine ⟨2964995964582753723181943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906655905554009928485181 2964995964582753723181943)
                      ·
                        rfl

theorem cell23_5774309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5774309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774309 prefixEnd_5774309 := by exact prefixLift 5774309
  have htrace : WordTrace (prefixWord ++ tailWord_5774309) baseStart_5774309 baseEnd_5774309 := by
    simpa [prefixWord, tailWord_5774309, baseEnd_5774309] using wordTrace_append hprefix tailTrace_5774309
  have hstable : (prefixWord ++ tailWord_5774309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774309).length < 2 ^ (prefixWord ++ tailWord_5774309).sum := by decide
  have hdescent : baseEnd_5774309 < baseStart_5774309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774418 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5774418 : Nat := 118140960795 + 5774418 * 2 ^ 59
def prefixEnd_5774418 : Nat := 4983230072969 + 3 ^ 40 * 5774418 * 2
def baseEnd_5774418 : Nat := 2965051933974093796718941

theorem tailTrace_5774418 : CollatzResearch.WordTrace tailWord_5774418 prefixEnd_5774418 2965051933974093796718941 := by
  unfold tailWord_5774418
  simp only [CollatzResearch.WordTrace]
  refine ⟨52652581698569313231186977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140406884529518168616498605 52652581698569313231186977)
  ·
    refine ⟨39489436273926984923390233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52652581698569313231186977 39489436273926984923390233)
    ·
      refine ⟨29617077205445238692542675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39489436273926984923390233 29617077205445238692542675)
      ·
        refine ⟨44425615808167858038814013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29617077205445238692542675 44425615808167858038814013)
        ·
          refine ⟨16659605928062946764555255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44425615808167858038814013 16659605928062946764555255)
          ·
            refine ⟨24989408892094420146832883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16659605928062946764555255 24989408892094420146832883)
            ·
              refine ⟨37484113338141630220249325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24989408892094420146832883 37484113338141630220249325)
              ·
                refine ⟨14056542501803111332593497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37484113338141630220249325 14056542501803111332593497)
                ·
                  refine ⟨10542406876352333499445123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14056542501803111332593497 10542406876352333499445123)
                  ·
                    refine ⟨15813610314528500249167685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10542406876352333499445123 15813610314528500249167685)
                    ·
                      refine ⟨2965051933974093796718941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15813610314528500249167685 2965051933974093796718941)
                      ·
                        rfl

theorem cell23_5774418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5774418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774418 prefixEnd_5774418 := by exact prefixLift 5774418
  have htrace : WordTrace (prefixWord ++ tailWord_5774418) baseStart_5774418 baseEnd_5774418 := by
    simpa [prefixWord, tailWord_5774418, baseEnd_5774418] using wordTrace_append hprefix tailTrace_5774418
  have hstable : (prefixWord ++ tailWord_5774418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774418).length < 2 ^ (prefixWord ++ tailWord_5774418).sum := by decide
  have hdescent : baseEnd_5774418 < baseStart_5774418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774441 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 6]
def baseStart_5774441 : Nat := 118140960795 + 5774441 * 2 ^ 59
def prefixEnd_5774441 : Nat := 4983230072969 + 3 ^ 40 * 5774441 * 2
def baseEnd_5774441 : Nat := 329451527114349689636815

theorem tailTrace_5774441 : CollatzResearch.WordTrace tailWord_5774441 prefixEnd_5774441 329451527114349689636815 := by
  unfold tailWord_5774441
  simp only [CollatzResearch.WordTrace]
  refine ⟨210611165673193927852835177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140407443782129285235223451 210611165673193927852835177)
  ·
    refine ⟨157958374254895445889626383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210611165673193927852835177 157958374254895445889626383)
    ·
      refine ⟨236937561382343168834439575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157958374254895445889626383 236937561382343168834439575)
      ·
        refine ⟨355406342073514753251659363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236937561382343168834439575 355406342073514753251659363)
        ·
          refine ⟨533109513110272129877489045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355406342073514753251659363 533109513110272129877489045)
          ·
            refine ⟨24989508427044006088007299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 533109513110272129877489045 24989508427044006088007299)
            ·
              refine ⟨37484262640566009132010949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24989508427044006088007299 37484262640566009132010949)
              ·
                refine ⟨7028299245106126712252053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37484262640566009132010949 7028299245106126712252053)
                ·
                  refine ⟨329451527114349689636815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7028299245106126712252053 329451527114349689636815)
                  ·
                    rfl

theorem cell23_5774441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 6].length) (baseStart_5774441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774441 prefixEnd_5774441 := by exact prefixLift 5774441
  have htrace : WordTrace (prefixWord ++ tailWord_5774441) baseStart_5774441 baseEnd_5774441 := by
    simpa [prefixWord, tailWord_5774441, baseEnd_5774441] using wordTrace_append hprefix tailTrace_5774441
  have hstable : (prefixWord ++ tailWord_5774441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774441).length < 2 ^ (prefixWord ++ tailWord_5774441).sum := by decide
  have hdescent : baseEnd_5774441 < baseStart_5774441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774472 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5774472 : Nat := 118140960795 + 5774472 * 2 ^ 59
def prefixEnd_5774472 : Nat := 4983230072969 + 3 ^ 40 * 5774472 * 2
def baseEnd_5774472 : Nat := 2965079661929436585443693

theorem tailTrace_5774472 : CollatzResearch.WordTrace tailWord_5774472 prefixEnd_5774472 2965079661929436585443693 := by
  unfold tailWord_5774472
  simp only [CollatzResearch.WordTrace]
  refine ⟨105306148168040810073606835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140408197557387746764809113 105306148168040810073606835)
  ·
    refine ⟨157959222252061215110410253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105306148168040810073606835 157959222252061215110410253)
    ·
      refine ⟨59234708344522955666403845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157959222252061215110410253 59234708344522955666403845)
      ·
        refine ⟨11106507814598054187450721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59234708344522955666403845 11106507814598054187450721)
        ·
          refine ⟨8329880860948540640588041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11106507814598054187450721 8329880860948540640588041)
          ·
            refine ⟨6247410645711405480441031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8329880860948540640588041 6247410645711405480441031)
            ·
              refine ⟨9371115968567108220661547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247410645711405480441031 9371115968567108220661547)
              ·
                refine ⟨14056673952850662330992321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9371115968567108220661547 14056673952850662330992321)
                ·
                  refine ⟨10542505464637996748244241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14056673952850662330992321 10542505464637996748244241)
                  ·
                    refine ⟨7906879098478497561183181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10542505464637996748244241 7906879098478497561183181)
                    ·
                      refine ⟨2965079661929436585443693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7906879098478497561183181 2965079661929436585443693)
                      ·
                        rfl

theorem cell23_5774472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5774472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774472 prefixEnd_5774472 := by exact prefixLift 5774472
  have htrace : WordTrace (prefixWord ++ tailWord_5774472) baseStart_5774472 baseEnd_5774472 := by
    simpa [prefixWord, tailWord_5774472, baseEnd_5774472] using wordTrace_append hprefix tailTrace_5774472
  have hstable : (prefixWord ++ tailWord_5774472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774472).length < 2 ^ (prefixWord ++ tailWord_5774472).sum := by decide
  have hdescent : baseEnd_5774472 < baseStart_5774472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4]
def baseStart_5774491 : Nat := 118140960795 + 5774491 * 2 ^ 59
def prefixEnd_5774491 : Nat := 4983230072969 + 3 ^ 40 * 5774491 * 2
def baseEnd_5774491 : Nat := 2965089418061872011106105

theorem tailTrace_5774491 : CollatzResearch.WordTrace tailWord_5774491 prefixEnd_5774491 2965089418061872011106105 := by
  unfold tailWord_5774491
  simp only [CollatzResearch.WordTrace]
  refine ⟨210612989323012786392155327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140408659548675190928103551 210612989323012786392155327)
  ·
    refine ⟨315919483984519179588232991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210612989323012786392155327 315919483984519179588232991)
    ·
      refine ⟨473879225976778769382349487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315919483984519179588232991 473879225976778769382349487)
      ·
        refine ⟨710818838965168154073524231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473879225976778769382349487 710818838965168154073524231)
        ·
          refine ⟨1066228258447752231110286347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710818838965168154073524231 1066228258447752231110286347)
          ·
            refine ⟨1599342387671628346665429521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066228258447752231110286347 1599342387671628346665429521)
            ·
              refine ⟨1199506790753721259999072141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599342387671628346665429521 1199506790753721259999072141)
              ·
                refine ⟨449815046532645472499652053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199506790753721259999072141 449815046532645472499652053)
                ·
                  refine ⟨10542540153108878261710595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 449815046532645472499652053 10542540153108878261710595)
                  ·
                    refine ⟨15813810229663317392565893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10542540153108878261710595 15813810229663317392565893)
                    ·
                      refine ⟨2965089418061872011106105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15813810229663317392565893 2965089418061872011106105)
                      ·
                        rfl

theorem cell23_5774491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_5774491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774491 prefixEnd_5774491 := by exact prefixLift 5774491
  have htrace : WordTrace (prefixWord ++ tailWord_5774491) baseStart_5774491 baseEnd_5774491 := by
    simpa [prefixWord, tailWord_5774491, baseEnd_5774491] using wordTrace_append hprefix tailTrace_5774491
  have hstable : (prefixWord ++ tailWord_5774491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774491).length < 2 ^ (prefixWord ++ tailWord_5774491).sum := by decide
  have hdescent : baseEnd_5774491 < baseStart_5774491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774511 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_5774511 : Nat := 118140960795 + 5774511 * 2 ^ 59
def prefixEnd_5774511 : Nat := 4983230072969 + 3 ^ 40 * 5774511 * 2
def baseEnd_5774511 : Nat := 2965099687674961932856013

theorem tailTrace_5774511 : CollatzResearch.WordTrace tailWord_5774511 prefixEnd_5774511 2965099687674961932856013 := by
  unfold tailWord_5774511
  simp only [CollatzResearch.WordTrace]
  refine ⟨210613718782940329807883387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140409145855293553205255591 210613718782940329807883387)
  ·
    refine ⟨315920578174410494711825081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210613718782940329807883387 315920578174410494711825081)
    ·
      refine ⟨236940433630807871033868811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315920578174410494711825081 236940433630807871033868811)
      ·
        refine ⟨355410650446211806550803217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236940433630807871033868811 355410650446211806550803217)
        ·
          refine ⟨266557987834658854913102413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355410650446211806550803217 266557987834658854913102413)
          ·
            refine ⟨99959245437997070592413405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266557987834658854913102413 99959245437997070592413405)
            ·
              refine ⟨37484717039248901472155027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99959245437997070592413405 37484717039248901472155027)
              ·
                refine ⟨56227075558873352208232541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37484717039248901472155027 56227075558873352208232541)
                ·
                  refine ⟨21085153334577507078087203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56227075558873352208232541 21085153334577507078087203)
                  ·
                    refine ⟨31627730001866260617130805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21085153334577507078087203 31627730001866260617130805)
                    ·
                      refine ⟨2965099687674961932856013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31627730001866260617130805 2965099687674961932856013)
                      ·
                        rfl

theorem cell23_5774511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_5774511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774511 prefixEnd_5774511 := by exact prefixLift 5774511
  have htrace : WordTrace (prefixWord ++ tailWord_5774511) baseStart_5774511 baseEnd_5774511 := by
    simpa [prefixWord, tailWord_5774511, baseEnd_5774511] using wordTrace_append hprefix tailTrace_5774511
  have hstable : (prefixWord ++ tailWord_5774511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774511).length < 2 ^ (prefixWord ++ tailWord_5774511).sum := by decide
  have hdescent : baseEnd_5774511 < baseStart_5774511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774585 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 3, 3, 2]
def baseStart_5774585 : Nat := 118140960795 + 5774585 * 2 ^ 59
def prefixEnd_5774585 : Nat := 4983230072969 + 3 ^ 40 * 5774585 * 2
def baseEnd_5774585 : Nat := 2965137685243394643330673

theorem tailTrace_5774585 : CollatzResearch.WordTrace tailWord_5774585 prefixEnd_5774585 2965137685243394643330673 := by
  unfold tailWord_5774585
  simp only [CollatzResearch.WordTrace]
  refine ⟨210616417784672240446077209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140410945189781493630718139 210616417784672240446077209)
  ·
    refine ⟨157962313338504180334557907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210616417784672240446077209 157962313338504180334557907)
    ·
      refine ⟨236943470007756270501836861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157962313338504180334557907 236943470007756270501836861)
      ·
        refine ⟨88853801252908601438188823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236943470007756270501836861 88853801252908601438188823)
        ·
          refine ⟨133280701879362902157283235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88853801252908601438188823 133280701879362902157283235)
          ·
            refine ⟨199921052819044353235924853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133280701879362902157283235 199921052819044353235924853)
            ·
              refine ⟨18742598701785408115867955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199921052819044353235924853 18742598701785408115867955)
              ·
                refine ⟨28113898052678112173801933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18742598701785408115867955 28113898052678112173801933)
                ·
                  refine ⟨10542711769754292065175725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28113898052678112173801933 10542711769754292065175725)
                  ·
                    refine ⟨3953516913657859524440897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10542711769754292065175725 3953516913657859524440897)
                    ·
                      refine ⟨2965137685243394643330673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953516913657859524440897 2965137685243394643330673)
                      ·
                        rfl

theorem cell23_5774585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_5774585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774585 prefixEnd_5774585 := by exact prefixLift 5774585
  have htrace : WordTrace (prefixWord ++ tailWord_5774585) baseStart_5774585 baseEnd_5774585 := by
    simpa [prefixWord, tailWord_5774585, baseEnd_5774585] using wordTrace_append hprefix tailTrace_5774585
  have hstable : (prefixWord ++ tailWord_5774585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774585).length < 2 ^ (prefixWord ++ tailWord_5774585).sum := by decide
  have hdescent : baseEnd_5774585 < baseStart_5774585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774611 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_5774611 : Nat := 118140960795 + 5774611 * 2 ^ 59
def prefixEnd_5774611 : Nat := 4983230072969 + 3 ^ 40 * 5774611 * 2
def baseEnd_5774611 : Nat := 2965151035740411541605553

theorem tailTrace_5774611 : CollatzResearch.WordTrace tailWord_5774611 prefixEnd_5774611 2965151035740411541605553 := by
  unfold tailWord_5774611
  simp only [CollatzResearch.WordTrace]
  refine ⟨210617366082578046886523687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140411577388385364591015791 210617366082578046886523687)
  ·
    refine ⟨315926049123867070329785531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210617366082578046886523687 315926049123867070329785531)
    ·
      refine ⟨473889073685800605494678297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315926049123867070329785531 473889073685800605494678297)
      ·
        refine ⟨355416805264350454121008723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473889073685800605494678297 355416805264350454121008723)
        ·
          refine ⟨533125207896525681181513085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355416805264350454121008723 533125207896525681181513085)
          ·
            refine ⟨199921952961197130443067407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533125207896525681181513085 199921952961197130443067407)
            ·
              refine ⟨299882929441795695664601111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199921952961197130443067407 299882929441795695664601111)
              ·
                refine ⟨449824394162693543496901667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299882929441795695664601111 449824394162693543496901667)
                ·
                  refine ⟨674736591244040315245352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449824394162693543496901667 674736591244040315245352501)
                  ·
                    refine ⟨63256555429128779554251797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 674736591244040315245352501 63256555429128779554251797)
                    ·
                      refine ⟨2965151035740411541605553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63256555429128779554251797 2965151035740411541605553)
                      ·
                        rfl

theorem cell23_5774611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_5774611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774611 prefixEnd_5774611 := by exact prefixLift 5774611
  have htrace : WordTrace (prefixWord ++ tailWord_5774611) baseStart_5774611 baseEnd_5774611 := by
    simpa [prefixWord, tailWord_5774611, baseEnd_5774611] using wordTrace_append hprefix tailTrace_5774611
  have hstable : (prefixWord ++ tailWord_5774611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774611).length < 2 ^ (prefixWord ++ tailWord_5774611).sum := by decide
  have hdescent : baseEnd_5774611 < baseStart_5774611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774615 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_5774615 : Nat := 118140960795 + 5774615 * 2 ^ 59
def prefixEnd_5774615 : Nat := 4983230072969 + 3 ^ 40 * 5774615 * 2
def baseEnd_5774615 : Nat := 2965153089663029525955535

theorem tailTrace_5774615 : CollatzResearch.WordTrace tailWord_5774615 prefixEnd_5774615 2965153089663029525955535 := by
  unfold tailWord_5774615
  simp only [CollatzResearch.WordTrace]
  refine ⟨210617511974563555569669299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140411674649709037046446199 210617511974563555569669299)
  ·
    refine ⟨315926267961845333354503949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210617511974563555569669299 315926267961845333354503949)
    ·
      refine ⟨118472350485692000007938981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315926267961845333354503949 118472350485692000007938981)
      ·
        refine ⟨22213565716067250001488559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118472350485692000007938981 22213565716067250001488559)
        ·
          refine ⟨33320348574100875002232839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22213565716067250001488559 33320348574100875002232839)
          ·
            refine ⟨49980522861151312503349259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33320348574100875002232839 49980522861151312503349259)
            ·
              refine ⟨74970784291726968755023889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49980522861151312503349259 74970784291726968755023889)
              ·
                refine ⟨56228088218795226566267917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74970784291726968755023889 56228088218795226566267917)
                ·
                  refine ⟨21085533082048209962350469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56228088218795226566267917 21085533082048209962350469)
                  ·
                    refine ⟨3953537452884039367940713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21085533082048209962350469 3953537452884039367940713)
                    ·
                      refine ⟨2965153089663029525955535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953537452884039367940713 2965153089663029525955535)
                      ·
                        rfl

theorem cell23_5774615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_5774615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774615 prefixEnd_5774615 := by exact prefixLift 5774615
  have htrace : WordTrace (prefixWord ++ tailWord_5774615) baseStart_5774615 baseEnd_5774615 := by
    simpa [prefixWord, tailWord_5774615, baseEnd_5774615] using wordTrace_append hprefix tailTrace_5774615
  have hstable : (prefixWord ++ tailWord_5774615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774615).length < 2 ^ (prefixWord ++ tailWord_5774615).sum := by decide
  have hdescent : baseEnd_5774615 < baseStart_5774615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774632 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5774632 : Nat := 118140960795 + 5774632 * 2 ^ 59
def prefixEnd_5774632 : Nat := 4983230072969 + 3 ^ 40 * 5774632 * 2
def baseEnd_5774632 : Nat := 2965161818834155959442957

theorem tailTrace_5774632 : CollatzResearch.WordTrace tailWord_5774632 prefixEnd_5774632 2965161818834155959442957 := by
  unfold tailWord_5774632
  simp only [CollatzResearch.WordTrace]
  refine ⟨105309066007750983736519075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140412088010334644982025433 105309066007750983736519075)
  ·
    refine ⟨157963599011626475604778613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105309066007750983736519075 157963599011626475604778613)
    ·
      refine ⟨14809087407339982087947995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157963599011626475604778613 14809087407339982087947995)
      ·
        refine ⟨22213631111009973131921993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14809087407339982087947995 22213631111009973131921993)
        ·
          refine ⟨16660223333257479848941495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22213631111009973131921993 16660223333257479848941495)
          ·
            refine ⟨24990334999886219773412243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16660223333257479848941495 24990334999886219773412243)
            ·
              refine ⟨37485502499829329660118365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24990334999886219773412243 37485502499829329660118365)
              ·
                refine ⟨14057063437435998622544387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37485502499829329660118365 14057063437435998622544387)
                ·
                  refine ⟨21085595156153997933816581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14057063437435998622544387 21085595156153997933816581)
                  ·
                    refine ⟨3953549091778874612590609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21085595156153997933816581 3953549091778874612590609)
                    ·
                      refine ⟨2965161818834155959442957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953549091778874612590609 2965161818834155959442957)
                      ·
                        rfl

theorem cell23_5774632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5774632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774632 prefixEnd_5774632 := by exact prefixLift 5774632
  have htrace : WordTrace (prefixWord ++ tailWord_5774632) baseStart_5774632 baseEnd_5774632 := by
    simpa [prefixWord, tailWord_5774632, baseEnd_5774632] using wordTrace_append hprefix tailTrace_5774632
  have hstable : (prefixWord ++ tailWord_5774632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774632).length < 2 ^ (prefixWord ++ tailWord_5774632).sum := by decide
  have hdescent : baseEnd_5774632 < baseStart_5774632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774648 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_5774648 : Nat := 118140960795 + 5774648 * 2 ^ 59
def prefixEnd_5774648 : Nat := 4983230072969 + 3 ^ 40 * 5774648 * 2
def baseEnd_5774648 : Nat := 2965170034524627896842883

theorem tailTrace_5774648 : CollatzResearch.WordTrace tailWord_5774648 prefixEnd_5774648 2965170034524627896842883 := by
  unfold tailWord_5774648
  simp only [CollatzResearch.WordTrace]
  refine ⟨105309357791722001102810299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140412477055629334803747065 105309357791722001102810299)
  ·
    refine ⟨157964036687583001654215449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105309357791722001102810299 157964036687583001654215449)
    ·
      refine ⟨118473027515687251240661587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157964036687583001654215449 118473027515687251240661587)
      ·
        refine ⟨177709541273530876860992381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118473027515687251240661587 177709541273530876860992381)
        ·
          refine ⟨66641077977574078822872143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177709541273530876860992381 66641077977574078822872143)
          ·
            refine ⟨99961616966361118234308215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66641077977574078822872143 99961616966361118234308215)
            ·
              refine ⟨149942425449541677351462323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99961616966361118234308215 149942425449541677351462323)
              ·
                refine ⟨224913638174312516027193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149942425449541677351462323 224913638174312516027193485)
                ·
                  refine ⟨84342614315367193510197557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224913638174312516027193485 84342614315367193510197557)
                  ·
                    refine ⟨7907120092065674391581021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84342614315367193510197557 7907120092065674391581021)
                    ·
                      refine ⟨2965170034524627896842883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907120092065674391581021 2965170034524627896842883)
                      ·
                        rfl

theorem cell23_5774648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_5774648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774648 prefixEnd_5774648 := by exact prefixLift 5774648
  have htrace : WordTrace (prefixWord ++ tailWord_5774648) baseStart_5774648 baseEnd_5774648 := by
    simpa [prefixWord, tailWord_5774648, baseEnd_5774648] using wordTrace_append hprefix tailTrace_5774648
  have hstable : (prefixWord ++ tailWord_5774648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774648).length < 2 ^ (prefixWord ++ tailWord_5774648).sum := by decide
  have hdescent : baseEnd_5774648 < baseStart_5774648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774653 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5774653 : Nat := 118140960795 + 5774653 * 2 ^ 59
def prefixEnd_5774653 : Nat := 4983230072969 + 3 ^ 40 * 5774653 * 2
def baseEnd_5774653 : Nat := 2965172601927900377280361

theorem tailTrace_5774653 : CollatzResearch.WordTrace tailWord_5774653 prefixEnd_5774653 2965172601927900377280361 := by
  unfold tailWord_5774653
  simp only [CollatzResearch.WordTrace]
  refine ⟨210618897948425888059552613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140412598632283925373035075 210618897948425888059552613)
  ·
    refine ⟨39491043365329854011166115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210618897948425888059552613 39491043365329854011166115)
    ·
      refine ⟨59236565047994781016749173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39491043365329854011166115 59236565047994781016749173)
      ·
        refine ⟨5553427973249510720320235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59236565047994781016749173 5553427973249510720320235)
        ·
          refine ⟨8330141959874266080480353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553427973249510720320235 8330141959874266080480353)
          ·
            refine ⟨6247606469905699560360265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8330141959874266080480353 6247606469905699560360265)
            ·
              refine ⟨4685704852429274670270199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247606469905699560360265 4685704852429274670270199)
              ·
                refine ⟨7028557278643912005405299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685704852429274670270199 7028557278643912005405299)
                ·
                  refine ⟨10542835917965868008107949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028557278643912005405299 10542835917965868008107949)
                  ·
                    refine ⟨3953563469237200503040481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10542835917965868008107949 3953563469237200503040481)
                    ·
                      refine ⟨2965172601927900377280361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953563469237200503040481 2965172601927900377280361)
                      ·
                        rfl

theorem cell23_5774653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5774653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774653 prefixEnd_5774653 := by exact prefixLift 5774653
  have htrace : WordTrace (prefixWord ++ tailWord_5774653) baseStart_5774653 baseEnd_5774653 := by
    simpa [prefixWord, tailWord_5774653, baseEnd_5774653] using wordTrace_append hprefix tailTrace_5774653
  have hstable : (prefixWord ++ tailWord_5774653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774653).length < 2 ^ (prefixWord ++ tailWord_5774653).sum := by decide
  have hdescent : baseEnd_5774653 < baseStart_5774653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774655 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 5]
def baseStart_5774655 : Nat := 118140960795 + 5774655 * 2 ^ 59
def prefixEnd_5774655 : Nat := 4983230072969 + 3 ^ 40 * 5774655 * 2
def baseEnd_5774655 : Nat := 329463736543245485495039

theorem tailTrace_5774655 : CollatzResearch.WordTrace tailWord_5774655 prefixEnd_5774655 329463736543245485495039 := by
  unfold tailWord_5774655
  simp only [CollatzResearch.WordTrace]
  refine ⟨210618970894418642401125419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140412647262945761600750279 210618970894418642401125419)
  ·
    refine ⟨315928456341627963601688129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210618970894418642401125419 315928456341627963601688129)
    ·
      refine ⟨236946342256220972701266097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315928456341627963601688129 236946342256220972701266097)
      ·
        refine ⟨177709756692165729525949573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236946342256220972701266097 177709756692165729525949573)
        ·
          refine ⟨33320579379781074286115545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177709756692165729525949573 33320579379781074286115545)
          ·
            refine ⟨24990434534835805714586659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33320579379781074286115545 24990434534835805714586659)
            ·
              refine ⟨37485651802253708571879989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24990434534835805714586659 37485651802253708571879989)
              ·
                refine ⟨3514279856461285178613749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37485651802253708571879989 3514279856461285178613749)
                ·
                  refine ⟨329463736543245485495039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514279856461285178613749 329463736543245485495039)
                  ·
                    rfl

theorem cell23_5774655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 5].length) (baseStart_5774655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774655 prefixEnd_5774655 := by exact prefixLift 5774655
  have htrace : WordTrace (prefixWord ++ tailWord_5774655) baseStart_5774655 baseEnd_5774655 := by
    simpa [prefixWord, tailWord_5774655, baseEnd_5774655] using wordTrace_append hprefix tailTrace_5774655
  have hstable : (prefixWord ++ tailWord_5774655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774655).length < 2 ^ (prefixWord ++ tailWord_5774655).sum := by decide
  have hdescent : baseEnd_5774655 < baseStart_5774655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774705 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_5774705 : Nat := 118140960795 + 5774705 * 2 ^ 59
def prefixEnd_5774705 : Nat := 4983230072969 + 3 ^ 40 * 5774705 * 2
def baseEnd_5774705 : Nat := 2965199302921934173830121

theorem tailTrace_5774705 : CollatzResearch.WordTrace tailWord_5774705 prefixEnd_5774705 2965199302921934173830121 := by
  unfold tailWord_5774705
  simp only [CollatzResearch.WordTrace]
  refine ⟨210620794544237500940445569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140413863029491667293630379 210620794544237500940445569)
  ·
    refine ⟨157965595908178125705334177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210620794544237500940445569 157965595908178125705334177)
    ·
      refine ⟨118474196931133594279000633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157965595908178125705334177 118474196931133594279000633)
      ·
        refine ⟨88855647698350195709250475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118474196931133594279000633 88855647698350195709250475)
        ·
          refine ⟨133283471547525293563875713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88855647698350195709250475 133283471547525293563875713)
          ·
            refine ⟨99962603660643970172906785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133283471547525293563875713 99962603660643970172906785)
            ·
              refine ⟨74971952745482977629680089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99962603660643970172906785 74971952745482977629680089)
              ·
                refine ⟨56228964559112233222260067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74971952745482977629680089 56228964559112233222260067)
                ·
                  refine ⟨84343446838668349833390101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56228964559112233222260067 84343446838668349833390101)
                  ·
                    refine ⟨3953599070562578898440161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84343446838668349833390101 3953599070562578898440161)
                    ·
                      refine ⟨2965199302921934173830121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953599070562578898440161 2965199302921934173830121)
                      ·
                        rfl

theorem cell23_5774705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_5774705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774705 prefixEnd_5774705 := by exact prefixLift 5774705
  have htrace : WordTrace (prefixWord ++ tailWord_5774705) baseStart_5774705 baseEnd_5774705 := by
    simpa [prefixWord, tailWord_5774705, baseEnd_5774705] using wordTrace_append hprefix tailTrace_5774705
  have hstable : (prefixWord ++ tailWord_5774705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774705).length < 2 ^ (prefixWord ++ tailWord_5774705).sum := by decide
  have hdescent : baseEnd_5774705 < baseStart_5774705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774725 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_5774725 : Nat := 118140960795 + 5774725 * 2 ^ 59
def prefixEnd_5774725 : Nat := 4983230072969 + 3 ^ 40 * 5774725 * 2
def baseEnd_5774725 : Nat := 2965209572535024095580029

theorem tailTrace_5774725 : CollatzResearch.WordTrace tailWord_5774725 prefixEnd_5774725 2965209572535024095580029 := by
  unfold tailWord_5774725
  simp only [CollatzResearch.WordTrace]
  refine ⟨210621524004165044356173629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140414349336110029570782419 210621524004165044356173629)
  ·
    refine ⟨78983071501561891633565111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210621524004165044356173629 78983071501561891633565111)
    ·
      refine ⟨118474607252342837450347667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78983071501561891633565111 118474607252342837450347667)
      ·
        refine ⟨177711910878514256175521501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118474607252342837450347667 177711910878514256175521501)
        ·
          refine ⟨66641966579442846065820563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177711910878514256175521501 66641966579442846065820563)
          ·
            refine ⟨99962949869164269098730845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66641966579442846065820563 99962949869164269098730845)
            ·
              refine ⟨37486106200936600912024067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99962949869164269098730845 37486106200936600912024067)
              ·
                refine ⟨56229159301404901368036101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37486106200936600912024067 56229159301404901368036101)
                ·
                  refine ⟨10542967369013419006506769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56229159301404901368036101 10542967369013419006506769)
                  ·
                    refine ⟨7907225526760064254880077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10542967369013419006506769 7907225526760064254880077)
                    ·
                      refine ⟨2965209572535024095580029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907225526760064254880077 2965209572535024095580029)
                      ·
                        rfl

theorem cell23_5774725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_5774725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774725 prefixEnd_5774725 := by exact prefixLift 5774725
  have htrace : WordTrace (prefixWord ++ tailWord_5774725) baseStart_5774725 baseEnd_5774725 := by
    simpa [prefixWord, tailWord_5774725, baseEnd_5774725] using wordTrace_append hprefix tailTrace_5774725
  have hstable : (prefixWord ++ tailWord_5774725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774725).length < 2 ^ (prefixWord ++ tailWord_5774725).sum := by decide
  have hdescent : baseEnd_5774725 < baseStart_5774725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774745 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 6]
def baseStart_5774745 : Nat := 118140960795 + 5774745 * 2 ^ 59
def prefixEnd_5774745 : Nat := 4983230072969 + 3 ^ 40 * 5774745 * 2
def baseEnd_5774745 : Nat := 329468871349790446369993

theorem tailTrace_5774745 : CollatzResearch.WordTrace tailWord_5774745 prefixEnd_5774745 329468871349790446369993 := by
  unfold tailWord_5774745
  simp only [CollatzResearch.WordTrace]
  refine ⟨210622253464092587771901689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140414835642728391847934459 210622253464092587771901689)
  ·
    refine ⟨157966690098069440828926267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210622253464092587771901689 157966690098069440828926267)
    ·
      refine ⟨236950035147104161243389401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157966690098069440828926267 236950035147104161243389401)
      ·
        refine ⟨177712526360328120932542051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236950035147104161243389401 177712526360328120932542051)
        ·
          refine ⟨266568789540492181398813077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177712526360328120932542051 266568789540492181398813077)
          ·
            refine ⟨12495412009710571003069363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266568789540492181398813077 12495412009710571003069363)
            ·
              refine ⟨18743118014565856504604045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12495412009710571003069363 18743118014565856504604045)
              ·
                refine ⟨7028669255462196189226517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18743118014565856504604045 7028669255462196189226517)
                ·
                  refine ⟨329468871349790446369993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7028669255462196189226517 329468871349790446369993)
                  ·
                    rfl

theorem cell23_5774745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 6].length) (baseStart_5774745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774745 prefixEnd_5774745 := by exact prefixLift 5774745
  have htrace : WordTrace (prefixWord ++ tailWord_5774745) baseStart_5774745 baseEnd_5774745 := by
    simpa [prefixWord, tailWord_5774745, baseEnd_5774745] using wordTrace_append hprefix tailTrace_5774745
  have hstable : (prefixWord ++ tailWord_5774745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774745).length < 2 ^ (prefixWord ++ tailWord_5774745).sum := by decide
  have hdescent : baseEnd_5774745 < baseStart_5774745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774768 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_5774768 : Nat := 118140960795 + 5774768 * 2 ^ 59
def prefixEnd_5774768 : Nat := 4983230072969 + 3 ^ 40 * 5774768 * 2
def baseEnd_5774768 : Nat := 2965231652203167427342331

theorem tailTrace_5774768 : CollatzResearch.WordTrace tailWord_5774768 prefixEnd_5774768 2965231652203167427342331 := by
  unfold tailWord_5774768
  simp only [CollatzResearch.WordTrace]
  refine ⟨105311546171504631349994479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140415394895339508466659305 105311546171504631349994479)
  ·
    refine ⟨157967319257256947024991719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105311546171504631349994479 157967319257256947024991719)
    ·
      refine ⟨236950978885885420537487579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157967319257256947024991719 236950978885885420537487579)
      ·
        refine ⟨355426468328828130806231369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236950978885885420537487579 355426468328828130806231369)
        ·
          refine ⟨266569851246621098104673527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355426468328828130806231369 266569851246621098104673527)
          ·
            refine ⟨399854776869931647157010291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266569851246621098104673527 399854776869931647157010291)
            ·
              refine ⟨599782165304897470735515437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399854776869931647157010291 599782165304897470735515437)
              ·
                refine ⟨224918311989336551525818289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 599782165304897470735515437 224918311989336551525818289)
                ·
                  refine ⟨168688733992002413644363717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224918311989336551525818289 168688733992002413644363717)
                  ·
                    refine ⟨31629137623500452558318197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168688733992002413644363717 31629137623500452558318197)
                    ·
                      refine ⟨2965231652203167427342331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31629137623500452558318197 2965231652203167427342331)
                      ·
                        rfl

theorem cell23_5774768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_5774768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774768 prefixEnd_5774768 := by exact prefixLift 5774768
  have htrace : WordTrace (prefixWord ++ tailWord_5774768) baseStart_5774768 baseEnd_5774768 := by
    simpa [prefixWord, tailWord_5774768, baseEnd_5774768] using wordTrace_append hprefix tailTrace_5774768
  have hstable : (prefixWord ++ tailWord_5774768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774768).length < 2 ^ (prefixWord ++ tailWord_5774768).sum := by decide
  have hdescent : baseEnd_5774768 < baseStart_5774768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774782 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_5774782 : Nat := 118140960795 + 5774782 * 2 ^ 59
def prefixEnd_5774782 : Nat := 4983230072969 + 3 ^ 40 * 5774782 * 2
def baseEnd_5774782 : Nat := 2965238840932330372567267

theorem tailTrace_5774782 : CollatzResearch.WordTrace tailWord_5774782 prefixEnd_5774782 2965238840932330372567267 := by
  unfold tailWord_5774782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26327950370619817886374825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140415735309972362060665733 26327950370619817886374825)
  ·
    refine ⟨19745962777964863414781119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26327950370619817886374825 19745962777964863414781119)
    ·
      refine ⟨29618944166947295122171679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19745962777964863414781119 29618944166947295122171679)
      ·
        refine ⟨44428416250420942683257519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29618944166947295122171679 44428416250420942683257519)
        ·
          refine ⟨66642624375631414024886279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44428416250420942683257519 66642624375631414024886279)
          ·
            refine ⟨99963936563447121037329419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66642624375631414024886279 99963936563447121037329419)
            ·
              refine ⟨149945904845170681555994129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99963936563447121037329419 149945904845170681555994129)
              ·
                refine ⟨112459428633878011166995597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149945904845170681555994129 112459428633878011166995597)
                ·
                  refine ⟨42172285737704254187623349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112459428633878011166995597 42172285737704254187623349)
                  ·
                    refine ⟨3953651787909773830089689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42172285737704254187623349 3953651787909773830089689)
                    ·
                      refine ⟨2965238840932330372567267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953651787909773830089689 2965238840932330372567267)
                      ·
                        rfl

theorem cell23_5774782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_5774782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774782 prefixEnd_5774782 := by exact prefixLift 5774782
  have htrace : WordTrace (prefixWord ++ tailWord_5774782) baseStart_5774782 baseEnd_5774782 := by
    simpa [prefixWord, tailWord_5774782, baseEnd_5774782] using wordTrace_append hprefix tailTrace_5774782
  have hstable : (prefixWord ++ tailWord_5774782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774782).length < 2 ^ (prefixWord ++ tailWord_5774782).sum := by decide
  have hdescent : baseEnd_5774782 < baseStart_5774782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774795 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4]
def baseStart_5774795 : Nat := 118140960795 + 5774795 * 2 ^ 59
def prefixEnd_5774795 : Nat := 4983230072969 + 3 ^ 40 * 5774795 * 2
def baseEnd_5774795 : Nat := 2965245516180838821704707

theorem tailTrace_5774795 : CollatzResearch.WordTrace tailWord_5774795 prefixEnd_5774795 2965245516180838821704707 := by
  unfold tailWord_5774795
  simp only [CollatzResearch.WordTrace]
  refine ⟨210624077113911446311221839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140416051409274297540814559 210624077113911446311221839)
  ·
    refine ⟨315936115670867169466832759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210624077113911446311221839 315936115670867169466832759)
    ·
      refine ⟨473904173506300754200249139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315936115670867169466832759 473904173506300754200249139)
      ·
        refine ⟨710856260259451131300373709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473904173506300754200249139 710856260259451131300373709)
        ·
          refine ⟨266571097597294174237640141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 710856260259451131300373709 266571097597294174237640141)
          ·
            refine ⟨99964161598985315339115053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266571097597294174237640141 99964161598985315339115053)
            ·
              refine ⟨37486560599619493252168145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99964161598985315339115053 37486560599619493252168145)
              ·
                refine ⟨28114920449714619939126109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37486560599619493252168145 28114920449714619939126109)
                ·
                  refine ⟨10543095168642982477172291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28114920449714619939126109 10543095168642982477172291)
                  ·
                    refine ⟨15814642752964473715758437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10543095168642982477172291 15814642752964473715758437)
                    ·
                      refine ⟨2965245516180838821704707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15814642752964473715758437 2965245516180838821704707)
                      ·
                        rfl

theorem cell23_5774795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_5774795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774795 prefixEnd_5774795 := by exact prefixLift 5774795
  have htrace : WordTrace (prefixWord ++ tailWord_5774795) baseStart_5774795 baseEnd_5774795 := by
    simpa [prefixWord, tailWord_5774795, baseEnd_5774795] using wordTrace_append hprefix tailTrace_5774795
  have hstable : (prefixWord ++ tailWord_5774795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774795).length < 2 ^ (prefixWord ++ tailWord_5774795).sum := by decide
  have hdescent : baseEnd_5774795 < baseStart_5774795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774806 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_5774806 : Nat := 118140960795 + 5774806 * 2 ^ 59
def prefixEnd_5774806 : Nat := 4983230072969 + 3 ^ 40 * 5774806 * 2
def baseEnd_5774806 : Nat := 2965251164468038278667157

theorem tailTrace_5774806 : CollatzResearch.WordTrace tailWord_5774806 prefixEnd_5774806 2965251164468038278667157 := by
  unfold tailWord_5774806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164029894804474699367017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140416318877914396793248181 13164029894804474699367017)
  ·
    refine ⟨9873022421103356024525263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13164029894804474699367017 9873022421103356024525263)
    ·
      refine ⟨14809533631655034036787895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9873022421103356024525263 14809533631655034036787895)
      ·
        refine ⟨22214300447482551055181843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14809533631655034036787895 22214300447482551055181843)
        ·
          refine ⟨33321450671223826582772765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22214300447482551055181843 33321450671223826582772765)
          ·
            refine ⟨12495544001708934968539787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33321450671223826582772765 12495544001708934968539787)
            ·
              refine ⟨18743316002563402452809681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12495544001708934968539787 18743316002563402452809681)
              ·
                refine ⟨14057487001922551839607261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18743316002563402452809681 14057487001922551839607261)
                ·
                  refine ⟨5271557625720956939852723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14057487001922551839607261 5271557625720956939852723)
                  ·
                    refine ⟨7907336438581435409779085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5271557625720956939852723 7907336438581435409779085)
                    ·
                      refine ⟨2965251164468038278667157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907336438581435409779085 2965251164468038278667157)
                      ·
                        rfl

theorem cell23_5774806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_5774806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774806 prefixEnd_5774806 := by exact prefixLift 5774806
  have htrace : WordTrace (prefixWord ++ tailWord_5774806) baseStart_5774806 baseEnd_5774806 := by
    simpa [prefixWord, tailWord_5774806, baseEnd_5774806] using wordTrace_append hprefix tailTrace_5774806
  have hstable : (prefixWord ++ tailWord_5774806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774806).length < 2 ^ (prefixWord ++ tailWord_5774806).sum := by decide
  have hdescent : baseEnd_5774806 < baseStart_5774806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774826 : List Nat := [3, 1, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_5774826 : Nat := 118140960795 + 5774826 * 2 ^ 59
def prefixEnd_5774826 : Nat := 4983230072969 + 3 ^ 40 * 5774826 * 2
def baseEnd_5774826 : Nat := 988420478027042733472355

theorem tailTrace_5774826 : CollatzResearch.WordTrace tailWord_5774826 prefixEnd_5774826 988420478027042733472355 := by
  unfold tailWord_5774826
  simp only [CollatzResearch.WordTrace]
  refine ⟨52656301944199784651400083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140416805184532759070400221 52656301944199784651400083)
  ·
    refine ⟨78984452916299676977100125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52656301944199784651400083 78984452916299676977100125)
    ·
      refine ⟨29619169843612378866412547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78984452916299676977100125 29619169843612378866412547)
      ·
        refine ⟨44428754765418568299618821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29619169843612378866412547 44428754765418568299618821)
        ·
          refine ⟨8330391518515981556178529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44428754765418568299618821 8330391518515981556178529)
          ·
            refine ⟨6247793638886986167133897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8330391518515981556178529 6247793638886986167133897)
            ·
              refine ⟨4685845229165239625350423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247793638886986167133897 4685845229165239625350423)
              ·
                refine ⟨7028767843747859438025635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685845229165239625350423 7028767843747859438025635)
                ·
                  refine ⟨10543151765621789157038453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028767843747859438025635 10543151765621789157038453)
                  ·
                    refine ⟨988420478027042733472355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10543151765621789157038453 988420478027042733472355)
                    ·
                      rfl

theorem cell23_5774826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_5774826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774826 prefixEnd_5774826 := by exact prefixLift 5774826
  have htrace : WordTrace (prefixWord ++ tailWord_5774826) baseStart_5774826 baseEnd_5774826 := by
    simpa [prefixWord, tailWord_5774826, baseEnd_5774826] using wordTrace_append hprefix tailTrace_5774826
  have hstable : (prefixWord ++ tailWord_5774826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774826).length < 2 ^ (prefixWord ++ tailWord_5774826).sum := by decide
  have hdescent : baseEnd_5774826 < baseStart_5774826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774859 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 4]
def baseStart_5774859 : Nat := 118140960795 + 5774859 * 2 ^ 59
def prefixEnd_5774859 : Nat := 4983230072969 + 3 ^ 40 * 5774859 * 2
def baseEnd_5774859 : Nat := 2965278378942726571304413

theorem tailTrace_5774859 : CollatzResearch.WordTrace tailWord_5774859 prefixEnd_5774859 2965278378942726571304413 := by
  unfold tailWord_5774859
  simp only [CollatzResearch.WordTrace]
  refine ⟨210626411385679585241551631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140417607590453056827701087 210626411385679585241551631)
  ·
    refine ⟨315939617078519377862327447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210626411385679585241551631 315939617078519377862327447)
    ·
      refine ⟨473909425617779066793491171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315939617078519377862327447 473909425617779066793491171)
      ·
        refine ⟨710864138426668600190236757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473909425617779066793491171 710864138426668600190236757)
        ·
          refine ⟨8330439122187522658479337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 710864138426668600190236757 8330439122187522658479337)
          ·
            refine ⟨6247829341640641993859503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8330439122187522658479337 6247829341640641993859503)
            ·
              refine ⟨9371744012460962990789255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247829341640641993859503 9371744012460962990789255)
              ·
                refine ⟨14057616018691444486183883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9371744012460962990789255 14057616018691444486183883)
                ·
                  refine ⟨21086424028037166729275825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14057616018691444486183883 21086424028037166729275825)
                  ·
                    refine ⟨15814818021027875046956869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21086424028037166729275825 15814818021027875046956869)
                    ·
                      refine ⟨2965278378942726571304413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15814818021027875046956869 2965278378942726571304413)
                      ·
                        rfl

theorem cell23_5774859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 4].length) (baseStart_5774859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774859 prefixEnd_5774859 := by exact prefixLift 5774859
  have htrace : WordTrace (prefixWord ++ tailWord_5774859) baseStart_5774859 baseEnd_5774859 := by
    simpa [prefixWord, tailWord_5774859, baseEnd_5774859] using wordTrace_append hprefix tailTrace_5774859
  have hstable : (prefixWord ++ tailWord_5774859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774859).length < 2 ^ (prefixWord ++ tailWord_5774859).sum := by decide
  have hdescent : baseEnd_5774859 < baseStart_5774859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774880 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5774880 : Nat := 118140960795 + 5774880 * 2 ^ 59
def prefixEnd_5774880 : Nat := 4983230072969 + 3 ^ 40 * 5774880 * 2
def baseEnd_5774880 : Nat := 2965289162036470989141817

theorem tailTrace_5774880 : CollatzResearch.WordTrace tailWord_5774880 prefixEnd_5774880 2965289162036470989141817 := by
  unfold tailWord_5774880
  simp only [CollatzResearch.WordTrace]
  refine ⟨105313588659301752914033047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140418118212402337218710729 105313588659301752914033047)
  ·
    refine ⟨157970382988952629371049571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105313588659301752914033047 157970382988952629371049571)
    ·
      refine ⟨236955574483428944056574357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157970382988952629371049571 236955574483428944056574357)
      ·
        refine ⟨11107292553910731752651923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236955574483428944056574357 11107292553910731752651923)
        ·
          refine ⟨16660938830866097628977885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11107292553910731752651923 16660938830866097628977885)
          ·
            refine ⟨6247852061574786610866707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16660938830866097628977885 6247852061574786610866707)
            ·
              refine ⟨9371778092362179916300061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6247852061574786610866707 9371778092362179916300061)
              ·
                refine ⟨3514416784635817468612523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9371778092362179916300061 3514416784635817468612523)
                ·
                  refine ⟨5271625176953726202918785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514416784635817468612523 5271625176953726202918785)
                  ·
                    refine ⟨3953718882715294652189089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5271625176953726202918785 3953718882715294652189089)
                    ·
                      refine ⟨2965289162036470989141817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953718882715294652189089 2965289162036470989141817)
                      ·
                        rfl

theorem cell23_5774880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5774880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774880 prefixEnd_5774880 := by exact prefixLift 5774880
  have htrace : WordTrace (prefixWord ++ tailWord_5774880) baseStart_5774880 baseEnd_5774880 := by
    simpa [prefixWord, tailWord_5774880, baseEnd_5774880] using wordTrace_append hprefix tailTrace_5774880
  have hstable : (prefixWord ++ tailWord_5774880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774880).length < 2 ^ (prefixWord ++ tailWord_5774880).sum := by decide
  have hdescent : baseEnd_5774880 < baseStart_5774880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774885 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_5774885 : Nat := 118140960795 + 5774885 * 2 ^ 59
def prefixEnd_5774885 : Nat := 4983230072969 + 3 ^ 40 * 5774885 * 2
def baseEnd_5774885 : Nat := 2965291729439743469579293

theorem tailTrace_5774885 : CollatzResearch.WordTrace tailWord_5774885 prefixEnd_5774885 2965291729439743469579293 := by
  unfold tailWord_5774885
  simp only [CollatzResearch.WordTrace]
  refine ⟨210627359683585391681998109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140418239789056927787998739 210627359683585391681998109)
  ·
    refine ⟨78985259881344521880749291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210627359683585391681998109 78985259881344521880749291)
    ·
      refine ⟨118477889822016782821123937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78985259881344521880749291 118477889822016782821123937)
      ·
        refine ⟨88858417366512587115842953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118477889822016782821123937 88858417366512587115842953)
        ·
          refine ⟨66643813024884440336882215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88858417366512587115842953 66643813024884440336882215)
          ·
            refine ⟨99965719537326660505323323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66643813024884440336882215 99965719537326660505323323)
            ·
              refine ⟨149948579305989990757984985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99965719537326660505323323 149948579305989990757984985)
              ·
                refine ⟨112461434479492493068488739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149948579305989990757984985 112461434479492493068488739)
                ·
                  refine ⟨168692151719238739602733109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112461434479492493068488739 168692151719238739602733109)
                  ·
                    refine ⟨15814889223678631837756229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168692151719238739602733109 15814889223678631837756229)
                    ·
                      refine ⟨2965291729439743469579293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15814889223678631837756229 2965291729439743469579293)
                      ·
                        rfl

theorem cell23_5774885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_5774885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774885 prefixEnd_5774885 := by exact prefixLift 5774885
  have htrace : WordTrace (prefixWord ++ tailWord_5774885) baseStart_5774885 baseEnd_5774885 := by
    simpa [prefixWord, tailWord_5774885, baseEnd_5774885] using wordTrace_append hprefix tailTrace_5774885
  have hstable : (prefixWord ++ tailWord_5774885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774885).length < 2 ^ (prefixWord ++ tailWord_5774885).sum := by decide
  have hdescent : baseEnd_5774885 < baseStart_5774885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5774995 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_5774995 : Nat := 118140960795 + 5774995 * 2 ^ 59
def prefixEnd_5774995 : Nat := 4983230072969 + 3 ^ 40 * 5774995 * 2
def baseEnd_5774995 : Nat := 2965348212311738039203787

theorem tailTrace_5774995 : CollatzResearch.WordTrace tailWord_5774995 prefixEnd_5774995 2965348212311738039203787 := by
  unfold tailWord_5774995
  simp only [CollatzResearch.WordTrace]
  refine ⟨210631371713186880468502439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140420914475457920312334959 210631371713186880468502439)
  ·
    refine ⟨315947057569780320702753659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210631371713186880468502439 315947057569780320702753659)
    ·
      refine ⟨473920586354670481054130489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315947057569780320702753659 473920586354670481054130489)
      ·
        refine ⟨355440439766002860790597867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473920586354670481054130489 355440439766002860790597867)
        ·
          refine ⟨533160659649004291185896801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355440439766002860790597867 533160659649004291185896801)
          ·
            refine ⟨399870494736753218389422601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533160659649004291185896801 399870494736753218389422601)
            ·
              refine ⟨299902871052564913792066951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399870494736753218389422601 299902871052564913792066951)
              ·
                refine ⟨449854306578847370688100427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299902871052564913792066951 449854306578847370688100427)
                ·
                  refine ⟨674781459868271056032150641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449854306578847370688100427 674781459868271056032150641)
                  ·
                    refine ⟨506086094901203292024112981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 674781459868271056032150641 506086094901203292024112981)
                    ·
                      refine ⟨2965348212311738039203787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 506086094901203292024112981 2965348212311738039203787)
                      ·
                        rfl

theorem cell23_5774995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_5774995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5774995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5774995 prefixEnd_5774995 := by exact prefixLift 5774995
  have htrace : WordTrace (prefixWord ++ tailWord_5774995) baseStart_5774995 baseEnd_5774995 := by
    simpa [prefixWord, tailWord_5774995, baseEnd_5774995] using wordTrace_append hprefix tailTrace_5774995
  have hstable : (prefixWord ++ tailWord_5774995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5774995).length < 2 ^ (prefixWord ++ tailWord_5774995).sum := by decide
  have hdescent : baseEnd_5774995 < baseStart_5774995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5774995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775032 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 6]
def baseStart_5775032 : Nat := 118140960795 + 5775032 * 2 ^ 59
def prefixEnd_5775032 : Nat := 4983230072969 + 3 ^ 40 * 5775032 * 2
def baseEnd_5775032 : Nat := 329485245677328266049013

theorem tailTrace_5775032 : CollatzResearch.WordTrace tailWord_5775032 prefixEnd_5775032 329485245677328266049013 := by
  unfold tailWord_5775032
  simp only [CollatzResearch.WordTrace]
  refine ⟨105316360607026417893799675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140421814142701890525066233 105316360607026417893799675)
  ·
    refine ⟨157974540910539626840699513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105316360607026417893799675 157974540910539626840699513)
    ·
      refine ⟨118480905682904720130524635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157974540910539626840699513 118480905682904720130524635)
      ·
        refine ⟨177721358524357080195786953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118480905682904720130524635 177721358524357080195786953)
        ·
          refine ⟨133291018893267810146840215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177721358524357080195786953 133291018893267810146840215)
          ·
            refine ⟨199936528339901715220260323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133291018893267810146840215 199936528339901715220260323)
            ·
              refine ⟨299904792509852572830390485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199936528339901715220260323 299904792509852572830390485)
              ·
                refine ⟨7029018574449669675712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 299904792509852572830390485 7029018574449669675712277)
                ·
                  refine ⟨329485245677328266049013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7029018574449669675712277 329485245677328266049013)
                  ·
                    rfl

theorem cell23_5775032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 6].length) (baseStart_5775032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775032 prefixEnd_5775032 := by exact prefixLift 5775032
  have htrace : WordTrace (prefixWord ++ tailWord_5775032) baseStart_5775032 baseEnd_5775032 := by
    simpa [prefixWord, tailWord_5775032, baseEnd_5775032] using wordTrace_append hprefix tailTrace_5775032
  have hstable : (prefixWord ++ tailWord_5775032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775032).length < 2 ^ (prefixWord ++ tailWord_5775032).sum := by decide
  have hdescent : baseEnd_5775032 < baseStart_5775032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775086 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_5775086 : Nat := 118140960795 + 5775086 * 2 ^ 59
def prefixEnd_5775086 : Nat := 4983230072969 + 3 ^ 40 * 5775086 * 2
def baseEnd_5775086 : Nat := 2965394939051297183165869

theorem tailTrace_5775086 : CollatzResearch.WordTrace tailWord_5775086 prefixEnd_5775086 2965394939051297183165869 := by
  unfold tailWord_5775086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329336344482150376258139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140423127170571468673376741 26329336344482150376258139)
  ·
    refine ⟨39494004516723225564387209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26329336344482150376258139 39494004516723225564387209)
    ·
      refine ⟨29620503387542419173290407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39494004516723225564387209 29620503387542419173290407)
      ·
        refine ⟨44430755081313628759935611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29620503387542419173290407 44430755081313628759935611)
        ·
          refine ⟨66646132621970443139903417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44430755081313628759935611 66646132621970443139903417)
          ·
            refine ⟨49984599466477832354927563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66646132621970443139903417 49984599466477832354927563)
            ·
              refine ⟨74976899199716748532391345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49984599466477832354927563 74976899199716748532391345)
              ·
                refine ⟨56232674399787561399293509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74976899199716748532391345 56232674399787561399293509)
                ·
                  refine ⟨10543626449960167762367533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56232674399787561399293509 10543626449960167762367533)
                  ·
                    refine ⟨3953859918735062910887825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10543626449960167762367533 3953859918735062910887825)
                    ·
                      refine ⟨2965394939051297183165869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953859918735062910887825 2965394939051297183165869)
                      ·
                        rfl

theorem cell23_5775086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_5775086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775086 prefixEnd_5775086 := by exact prefixLift 5775086
  have htrace : WordTrace (prefixWord ++ tailWord_5775086) baseStart_5775086 baseEnd_5775086 := by
    simpa [prefixWord, tailWord_5775086, baseEnd_5775086] using wordTrace_append hprefix tailTrace_5775086
  have hstable : (prefixWord ++ tailWord_5775086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775086).length < 2 ^ (prefixWord ++ tailWord_5775086).sum := by decide
  have hdescent : baseEnd_5775086 < baseStart_5775086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 4]
def baseStart_5775099 : Nat := 118140960795 + 5775099 * 2 ^ 59
def prefixEnd_5775099 : Nat := 4983230072969 + 3 ^ 40 * 5775099 * 2
def baseEnd_5775099 : Nat := 2965401614299805632303309

theorem tailTrace_5775099 : CollatzResearch.WordTrace tailWord_5775099 prefixEnd_5775099 2965401614299805632303309 := by
  unfold tailWord_5775099
  simp only [CollatzResearch.WordTrace]
  refine ⟨210635164904810106230288351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140423443269873404153525567 210635164904810106230288351)
  ·
    refine ⟨315952747357215159345432527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210635164904810106230288351 315952747357215159345432527)
    ·
      refine ⟨473929121035822739018148791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315952747357215159345432527 473929121035822739018148791)
      ·
        refine ⟨710893681553734108527223187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473929121035822739018148791 710893681553734108527223187)
        ·
          refine ⟨1066340522330601162790834781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710893681553734108527223187 1066340522330601162790834781)
          ·
            refine ⟨399877695873975436046563043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1066340522330601162790834781 399877695873975436046563043)
            ·
              refine ⟨599816543810963154069844565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399877695873975436046563043 599816543810963154069844565)
              ·
                refine ⟨7029100122784724461755991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 599816543810963154069844565 7029100122784724461755991)
                ·
                  refine ⟨10543650184177086692633987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029100122784724461755991 10543650184177086692633987)
                  ·
                    refine ⟨15815475276265630038950981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10543650184177086692633987 15815475276265630038950981)
                    ·
                      refine ⟨2965401614299805632303309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15815475276265630038950981 2965401614299805632303309)
                      ·
                        rfl

theorem cell23_5775099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 4].length) (baseStart_5775099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775099 prefixEnd_5775099 := by exact prefixLift 5775099
  have htrace : WordTrace (prefixWord ++ tailWord_5775099) baseStart_5775099 baseEnd_5775099 := by
    simpa [prefixWord, tailWord_5775099, baseEnd_5775099] using wordTrace_append hprefix tailTrace_5775099
  have hstable : (prefixWord ++ tailWord_5775099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775099).length < 2 ^ (prefixWord ++ tailWord_5775099).sum := by decide
  have hdescent : baseEnd_5775099 < baseStart_5775099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775117 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5775117 : Nat := 118140960795 + 5775117 * 2 ^ 59
def prefixEnd_5775117 : Nat := 4983230072969 + 3 ^ 40 * 5775117 * 2
def baseEnd_5775117 : Nat := 329490095216842951319803

theorem tailTrace_5775117 : CollatzResearch.WordTrace tailWord_5775117 prefixEnd_5775117 329490095216842951319803 := by
  unfold tailWord_5775117
  simp only [CollatzResearch.WordTrace]
  refine ⟨210635821418744895304443605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140423880945829930202962403 210635821418744895304443605)
  ·
    refine ⟨4936777064501833483697897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 210635821418744895304443605 4936777064501833483697897)
    ·
      refine ⟨3702582798376375112773423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4936777064501833483697897 3702582798376375112773423)
      ·
        refine ⟨5553874197564562669160135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702582798376375112773423 5553874197564562669160135)
        ·
          refine ⟨8330811296346844003740203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5553874197564562669160135 8330811296346844003740203)
          ·
            refine ⟨12496216944520266005610305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330811296346844003740203 12496216944520266005610305)
            ·
              refine ⟨9372162708390199504207729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12496216944520266005610305 9372162708390199504207729)
              ·
                refine ⟨7029122031292649628155797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9372162708390199504207729 7029122031292649628155797)
                ·
                  refine ⟨329490095216842951319803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7029122031292649628155797 329490095216842951319803)
                  ·
                    rfl

theorem cell23_5775117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5775117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775117 prefixEnd_5775117 := by exact prefixLift 5775117
  have htrace : WordTrace (prefixWord ++ tailWord_5775117) baseStart_5775117 baseEnd_5775117 := by
    simpa [prefixWord, tailWord_5775117, baseEnd_5775117] using wordTrace_append hprefix tailTrace_5775117
  have hstable : (prefixWord ++ tailWord_5775117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775117).length < 2 ^ (prefixWord ++ tailWord_5775117).sum := by decide
  have hdescent : baseEnd_5775117 < baseStart_5775117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775127 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_5775127 : Nat := 118140960795 + 5775127 * 2 ^ 59
def prefixEnd_5775127 : Nat := 4983230072969 + 3 ^ 40 * 5775127 * 2
def baseEnd_5775127 : Nat := 2965415991758131522753181

theorem tailTrace_5775127 : CollatzResearch.WordTrace tailWord_5775127 prefixEnd_5775127 2965415991758131522753181 := by
  unfold tailWord_5775127
  simp only [CollatzResearch.WordTrace]
  refine ⟨210636186148708667012307635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140424124099139111341538423 210636186148708667012307635)
  ·
    refine ⟨315954279223063000518461453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210636186148708667012307635 315954279223063000518461453)
    ·
      refine ⟨118482854708648625194423045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315954279223063000518461453 118482854708648625194423045)
      ·
        refine ⟨22215535257871617223954321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118482854708648625194423045 22215535257871617223954321)
        ·
          refine ⟨16661651443403712917965741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22215535257871617223954321 16661651443403712917965741)
          ·
            refine ⟨6248119291276392344237153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16661651443403712917965741 6248119291276392344237153)
            ·
              refine ⟨4686089468457294258177865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248119291276392344237153 4686089468457294258177865)
              ·
                refine ⟨3514567101342970693633399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686089468457294258177865 3514567101342970693633399)
                ·
                  refine ⟨5271850652014456040450099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514567101342970693633399 5271850652014456040450099)
                  ·
                    refine ⟨7907775978021684060675149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5271850652014456040450099 7907775978021684060675149)
                    ·
                      refine ⟨2965415991758131522753181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907775978021684060675149 2965415991758131522753181)
                      ·
                        rfl

theorem cell23_5775127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_5775127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775127 prefixEnd_5775127 := by exact prefixLift 5775127
  have htrace : WordTrace (prefixWord ++ tailWord_5775127) baseStart_5775127 baseEnd_5775127 := by
    simpa [prefixWord, tailWord_5775127, baseEnd_5775127] using wordTrace_append hprefix tailTrace_5775127
  have hstable : (prefixWord ++ tailWord_5775127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775127).length < 2 ^ (prefixWord ++ tailWord_5775127).sum := by decide
  have hdescent : baseEnd_5775127 < baseStart_5775127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775167 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 1, 2, 2]
def baseStart_5775167 : Nat := 118140960795 + 5775167 * 2 ^ 59
def prefixEnd_5775167 : Nat := 4983230072969 + 3 ^ 40 * 5775167 * 2
def baseEnd_5775167 : Nat := 2965436530984311366252997

theorem tailTrace_5775167 : CollatzResearch.WordTrace tailWord_5775167 prefixEnd_5775167 2965436530984311366252997 := by
  unfold tailWord_5775167
  simp only [CollatzResearch.WordTrace]
  refine ⟨210637645068563753843763755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140425096712375835895842503 210637645068563753843763755)
  ·
    refine ⟨315956467602845630765645633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210637645068563753843763755 315956467602845630765645633)
    ·
      refine ⟨236967350702134223074234225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315956467602845630765645633 236967350702134223074234225)
      ·
        refine ⟨177725513026600667305675669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236967350702134223074234225 177725513026600667305675669)
        ·
          refine ⟨8330883423121906279953547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177725513026600667305675669 8330883423121906279953547)
          ·
            refine ⟨12496325134682859419930321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8330883423121906279953547 12496325134682859419930321)
            ·
              refine ⟨9372243851012144564947741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12496325134682859419930321 9372243851012144564947741)
              ·
                refine ⟨3514591444129554211855403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9372243851012144564947741 3514591444129554211855403)
                ·
                  refine ⟨5271887166194331317783105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514591444129554211855403 5271887166194331317783105)
                  ·
                    refine ⟨3953915374645748488337329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5271887166194331317783105 3953915374645748488337329)
                    ·
                      refine ⟨2965436530984311366252997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3953915374645748488337329 2965436530984311366252997)
                      ·
                        rfl

theorem cell23_5775167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_5775167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775167 prefixEnd_5775167 := by exact prefixLift 5775167
  have htrace : WordTrace (prefixWord ++ tailWord_5775167) baseStart_5775167 baseEnd_5775167 := by
    simpa [prefixWord, tailWord_5775167, baseEnd_5775167] using wordTrace_append hprefix tailTrace_5775167
  have hstable : (prefixWord ++ tailWord_5775167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775167).length < 2 ^ (prefixWord ++ tailWord_5775167).sum := by decide
  have hdescent : baseEnd_5775167 < baseStart_5775167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775199 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 2, 6]
def baseStart_5775199 : Nat := 118140960795 + 5775199 * 2 ^ 59
def prefixEnd_5775199 : Nat := 4983230072969 + 3 ^ 40 * 5775199 * 2
def baseEnd_5775199 : Nat := 988484320788418413684283

theorem tailTrace_5775199 : CollatzResearch.WordTrace tailWord_5775199 prefixEnd_5775199 988484320788418413684283 := by
  unfold tailWord_5775199
  simp only [CollatzResearch.WordTrace]
  refine ⟨210638812204447823308928651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140425874802965215539285767 210638812204447823308928651)
  ·
    refine ⟨315958218306671734963392977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210638812204447823308928651 315958218306671734963392977)
    ·
      refine ⟨236968663730003801222544733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315958218306671734963392977 236968663730003801222544733)
      ·
        refine ⟨88863248898751425458454275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236968663730003801222544733 88863248898751425458454275)
        ·
          refine ⟨133294873348127138187681413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88863248898751425458454275 133294873348127138187681413)
          ·
            refine ⟨24992788752773838410190265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133294873348127138187681413 24992788752773838410190265)
            ·
              refine ⟨18744591564580378807642699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24992788752773838410190265 18744591564580378807642699)
              ·
                refine ⟨28116887346870568211464049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18744591564580378807642699 28116887346870568211464049)
                ·
                  refine ⟨21087665510152926158598037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28116887346870568211464049 21087665510152926158598037)
                  ·
                    refine ⟨988484320788418413684283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21087665510152926158598037 988484320788418413684283)
                    ·
                      rfl

theorem cell23_5775199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_5775199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775199 prefixEnd_5775199 := by exact prefixLift 5775199
  have htrace : WordTrace (prefixWord ++ tailWord_5775199) baseStart_5775199 baseEnd_5775199 := by
    simpa [prefixWord, tailWord_5775199, baseEnd_5775199] using wordTrace_append hprefix tailTrace_5775199
  have hstable : (prefixWord ++ tailWord_5775199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775199).length < 2 ^ (prefixWord ++ tailWord_5775199).sum := by decide
  have hdescent : baseEnd_5775199 < baseStart_5775199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775200 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3]
def baseStart_5775200 : Nat := 118140960795 + 5775200 * 2 ^ 59
def prefixEnd_5775200 : Nat := 4983230072969 + 3 ^ 40 * 5775200 * 2
def baseEnd_5775200 : Nat := 2965453475845909737140345

theorem tailTrace_5775200 : CollatzResearch.WordTrace tailWord_5775200 prefixEnd_5775200 2965453475845909737140345 := by
  unfold tailWord_5775200
  simp only [CollatzResearch.WordTrace]
  refine ⟨105319424338722100239857527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140425899118296133653143369 105319424338722100239857527)
  ·
    refine ⟨157979136508083150359786291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105319424338722100239857527 157979136508083150359786291)
    ·
      refine ⟨236968704762124725539679437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157979136508083150359786291 236968704762124725539679437)
      ·
        refine ⟨88863264285796772077379789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236968704762124725539679437 88863264285796772077379789)
        ·
          refine ⟨33323724107173789529017421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88863264285796772077379789 33323724107173789529017421)
          ·
            refine ⟨12496396540190171073381533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33323724107173789529017421 12496396540190171073381533)
            ·
              refine ⟨4686148702571314152518075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12496396540190171073381533 4686148702571314152518075)
              ·
                refine ⟨7029223053856971228777113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686148702571314152518075 7029223053856971228777113)
                ·
                  refine ⟨5271917290392728421582835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7029223053856971228777113 5271917290392728421582835)
                  ·
                    refine ⟨7907875935589092632374253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5271917290392728421582835 7907875935589092632374253)
                    ·
                      refine ⟨2965453475845909737140345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907875935589092632374253 2965453475845909737140345)
                      ·
                        rfl

theorem cell23_5775200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_5775200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775200 prefixEnd_5775200 := by exact prefixLift 5775200
  have htrace : WordTrace (prefixWord ++ tailWord_5775200) baseStart_5775200 baseEnd_5775200 := by
    simpa [prefixWord, tailWord_5775200, baseEnd_5775200] using wordTrace_append hprefix tailTrace_5775200
  have hstable : (prefixWord ++ tailWord_5775200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775200).length < 2 ^ (prefixWord ++ tailWord_5775200).sum := by decide
  have hdescent : baseEnd_5775200 < baseStart_5775200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775209 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_5775209 : Nat := 118140960795 + 5775209 * 2 ^ 59
def prefixEnd_5775209 : Nat := 4983230072969 + 3 ^ 40 * 5775209 * 2
def baseEnd_5775209 : Nat := 2965458097171800201927803

theorem tailTrace_5775209 : CollatzResearch.WordTrace tailWord_5775209 prefixEnd_5775209 2965458097171800201927803 := by
  unfold tailWord_5775209
  simp only [CollatzResearch.WordTrace]
  refine ⟨210639176934411595016792681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140426117956274396677861787 210639176934411595016792681)
  ·
    refine ⟨157979382700808696262594511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210639176934411595016792681 157979382700808696262594511)
    ·
      refine ⟨236969074051213044393891767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157979382700808696262594511 236969074051213044393891767)
      ·
        refine ⟨355453611076819566590837651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236969074051213044393891767 355453611076819566590837651)
        ·
          refine ⟨533180416615229349886256477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355453611076819566590837651 533180416615229349886256477)
          ·
            refine ⟨199942656230711006207346179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533180416615229349886256477 199942656230711006207346179)
            ·
              refine ⟨299913984346066509311019269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199942656230711006207346179 299913984346066509311019269)
              ·
                refine ⟨56233872064887470495816113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 299913984346066509311019269 56233872064887470495816113)
                ·
                  refine ⟨42175404048665602871862085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56233872064887470495816113 42175404048665602871862085)
                  ·
                    refine ⟨7907888259124800538474141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42175404048665602871862085 7907888259124800538474141)
                    ·
                      refine ⟨2965458097171800201927803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7907888259124800538474141 2965458097171800201927803)
                      ·
                        rfl

theorem cell23_5775209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_5775209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775209 prefixEnd_5775209 := by exact prefixLift 5775209
  have htrace : WordTrace (prefixWord ++ tailWord_5775209) baseStart_5775209 baseEnd_5775209 := by
    simpa [prefixWord, tailWord_5775209, baseEnd_5775209] using wordTrace_append hprefix tailTrace_5775209
  have hstable : (prefixWord ++ tailWord_5775209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775209).length < 2 ^ (prefixWord ++ tailWord_5775209).sum := by decide
  have hdescent : baseEnd_5775209 < baseStart_5775209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775296 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_5775296 : Nat := 118140960795 + 5775296 * 2 ^ 59
def prefixEnd_5775296 : Nat := 4983230072969 + 3 ^ 40 * 5775296 * 2
def baseEnd_5775296 : Nat := 2965502769988741361539903

theorem tailTrace_5775296 : CollatzResearch.WordTrace tailWord_5775296 prefixEnd_5775296 2965502769988741361539903 := by
  unfold tailWord_5775296
  simp only [CollatzResearch.WordTrace]
  refine ⟨105321175042548204437604871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140428233390064272583473161 105321175042548204437604871)
  ·
    refine ⟨157981762563822306656407307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105321175042548204437604871 157981762563822306656407307)
    ·
      refine ⟨236972643845733459984610961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157981762563822306656407307 236972643845733459984610961)
      ·
        refine ⟨177729482884300094988458221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236972643845733459984610961 177729482884300094988458221)
        ·
          refine ⟨66648556081612535620671833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177729482884300094988458221 66648556081612535620671833)
          ·
            refine ⟨49986417061209401715503875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66648556081612535620671833 49986417061209401715503875)
            ·
              refine ⟨74979625591814102573255813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49986417061209401715503875 74979625591814102573255813)
              ·
                refine ⟨14058679798465144232485465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74979625591814102573255813 14058679798465144232485465)
                ·
                  refine ⟨10544009848848858174364099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14058679798465144232485465 10544009848848858174364099)
                  ·
                    refine ⟨15816014773273287261546149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10544009848848858174364099 15816014773273287261546149)
                    ·
                      refine ⟨2965502769988741361539903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15816014773273287261546149 2965502769988741361539903)
                      ·
                        rfl

theorem cell23_5775296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_5775296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775296 prefixEnd_5775296 := by exact prefixLift 5775296
  have htrace : WordTrace (prefixWord ++ tailWord_5775296) baseStart_5775296 baseEnd_5775296 := by
    simpa [prefixWord, tailWord_5775296, baseEnd_5775296] using wordTrace_append hprefix tailTrace_5775296
  have hstable : (prefixWord ++ tailWord_5775296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775296).length < 2 ^ (prefixWord ++ tailWord_5775296).sum := by decide
  have hdescent : baseEnd_5775296 < baseStart_5775296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775330 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5775330 : Nat := 118140960795 + 5775330 * 2 ^ 59
def prefixEnd_5775330 : Nat := 4983230072969 + 3 ^ 40 * 5775330 * 2
def baseEnd_5775330 : Nat := 2965520228330994228514747

theorem tailTrace_5775330 : CollatzResearch.WordTrace tailWord_5775330 prefixEnd_5775330 2965520228330994228514747 := by
  unfold tailWord_5775330
  simp only [CollatzResearch.WordTrace]
  refine ⟨52660897541743308170486861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140429060111315488454631629 52660897541743308170486861)
  ·
    refine ⟨19747836578153740563932573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52660897541743308170486861 19747836578153740563932573)
    ·
      refine ⟨7405438716807652711474715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19747836578153740563932573 7405438716807652711474715)
      ·
        refine ⟨11108158075211479067212073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7405438716807652711474715 11108158075211479067212073)
        ·
          refine ⟨8331118556408609300409055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11108158075211479067212073 8331118556408609300409055)
          ·
            refine ⟨12496677834612913950613583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331118556408609300409055 12496677834612913950613583)
            ·
              refine ⟨18745016751919370925920375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12496677834612913950613583 18745016751919370925920375)
              ·
                refine ⟨28117525127879056388880563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18745016751919370925920375 28117525127879056388880563)
                ·
                  refine ⟨42176287691818584583320845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28117525127879056388880563 42176287691818584583320845)
                  ·
                    refine ⟨15816107884431969218745317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42176287691818584583320845 15816107884431969218745317)
                    ·
                      refine ⟨2965520228330994228514747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15816107884431969218745317 2965520228330994228514747)
                      ·
                        rfl

theorem cell23_5775330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5775330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775330 prefixEnd_5775330 := by exact prefixLift 5775330
  have htrace : WordTrace (prefixWord ++ tailWord_5775330) baseStart_5775330 baseEnd_5775330 := by
    simpa [prefixWord, tailWord_5775330, baseEnd_5775330] using wordTrace_append hprefix tailTrace_5775330
  have hstable : (prefixWord ++ tailWord_5775330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775330).length < 2 ^ (prefixWord ++ tailWord_5775330).sum := by decide
  have hdescent : baseEnd_5775330 < baseStart_5775330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775339 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_5775339 : Nat := 118140960795 + 5775339 * 2 ^ 59
def prefixEnd_5775339 : Nat := 4983230072969 + 3 ^ 40 * 5775339 * 2
def baseEnd_5775339 : Nat := 2965524849656884693302205

theorem tailTrace_5775339 : CollatzResearch.WordTrace tailWord_5775339 prefixEnd_5775339 2965524849656884693302205 := by
  unfold tailWord_5775339
  simp only [CollatzResearch.WordTrace]
  refine ⟨210643918423940627219025071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140429278949293751479350047 210643918423940627219025071)
  ·
    refine ⟨315965877635910940828537607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210643918423940627219025071 315965877635910940828537607)
    ·
      refine ⟨473948816453866411242806411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315965877635910940828537607 473948816453866411242806411)
      ·
        refine ⟨710923224680799616864209617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473948816453866411242806411 710923224680799616864209617)
        ·
          refine ⟨533192418510599712648157213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710923224680799616864209617 533192418510599712648157213)
          ·
            refine ⟨199947156941474892243058955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533192418510599712648157213 199947156941474892243058955)
            ·
              refine ⟨299920735412212338364588433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199947156941474892243058955 299920735412212338364588433)
              ·
                refine ⟨224940551559159253773441325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299920735412212338364588433 224940551559159253773441325)
                ·
                  refine ⟨84352706834684720165040497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 224940551559159253773441325 84352706834684720165040497)
                  ·
                    refine ⟨63264530126013540123780373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84352706834684720165040497 63264530126013540123780373)
                    ·
                      refine ⟨2965524849656884693302205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63264530126013540123780373 2965524849656884693302205)
                      ·
                        rfl

theorem cell23_5775339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_5775339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775339 prefixEnd_5775339 := by exact prefixLift 5775339
  have htrace : WordTrace (prefixWord ++ tailWord_5775339) baseStart_5775339 baseEnd_5775339 := by
    simpa [prefixWord, tailWord_5775339, baseEnd_5775339] using wordTrace_append hprefix tailTrace_5775339
  have hstable : (prefixWord ++ tailWord_5775339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775339).length < 2 ^ (prefixWord ++ tailWord_5775339).sum := by decide
  have hdescent : baseEnd_5775339 < baseStart_5775339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775353 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 6]
def baseStart_5775353 : Nat := 118140960795 + 5775353 * 2 ^ 59
def prefixEnd_5775353 : Nat := 4983230072969 + 3 ^ 40 * 5775353 * 2
def baseEnd_5775353 : Nat := 329503559820671959836349

theorem tailTrace_5775353 : CollatzResearch.WordTrace tailWord_5775353 prefixEnd_5775353 329503559820671959836349 := by
  unfold tailWord_5775353
  simp only [CollatzResearch.WordTrace]
  refine ⟨210644429045889907610034713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140429619363926605073356475 210644429045889907610034713)
  ·
    refine ⟨157983321784417430707526035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210644429045889907610034713 157983321784417430707526035)
    ·
      refine ⟨236974982676626146061289053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157983321784417430707526035 236974982676626146061289053)
      ·
        refine ⟨88865618503734804772983395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236974982676626146061289053 88865618503734804772983395)
        ·
          refine ⟨133298427755602207159475093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88865618503734804772983395 133298427755602207159475093)
          ·
            refine ⟨6248363801043853460600395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133298427755602207159475093 6248363801043853460600395)
            ·
              refine ⟨9372545701565780190900593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248363801043853460600395 9372545701565780190900593)
              ·
                refine ⟨7029409276174335143175445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9372545701565780190900593 7029409276174335143175445)
                ·
                  refine ⟨329503559820671959836349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7029409276174335143175445 329503559820671959836349)
                  ·
                    rfl

theorem cell23_5775353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 6].length) (baseStart_5775353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775353 prefixEnd_5775353 := by exact prefixLift 5775353
  have htrace : WordTrace (prefixWord ++ tailWord_5775353) baseStart_5775353 baseEnd_5775353 := by
    simpa [prefixWord, tailWord_5775353, baseEnd_5775353] using wordTrace_append hprefix tailTrace_5775353
  have hstable : (prefixWord ++ tailWord_5775353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775353).length < 2 ^ (prefixWord ++ tailWord_5775353).sum := by decide
  have hdescent : baseEnd_5775353 < baseStart_5775353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775370 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_5775370 : Nat := 118140960795 + 5775370 * 2 ^ 59
def prefixEnd_5775370 : Nat := 4983230072969 + 3 ^ 40 * 5775370 * 2
def baseEnd_5775370 : Nat := 329504529728574896890507

theorem tailTrace_5775370 : CollatzResearch.WordTrace tailWord_5775370 prefixEnd_5775370 329504529728574896890507 := by
  unfold tailWord_5775370
  simp only [CollatzResearch.WordTrace]
  refine ⟨52661262271707079878350891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140430032724552213008935709 52661262271707079878350891)
  ·
    refine ⟨78991893407560619817526337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52661262271707079878350891 78991893407560619817526337)
    ·
      refine ⟨59243920055670464863144753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78991893407560619817526337 59243920055670464863144753)
      ·
        refine ⟨44432940041752848647358565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59243920055670464863144753 44432940041752848647358565)
        ·
          refine ⟨8331176257828659121379731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44432940041752848647358565 8331176257828659121379731)
          ·
            refine ⟨12496764386742988682069597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331176257828659121379731 12496764386742988682069597)
            ·
              refine ⟨4686286645028620755776099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12496764386742988682069597 4686286645028620755776099)
              ·
                refine ⟨7029429967542931133664149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686286645028620755776099 7029429967542931133664149)
                ·
                  refine ⟨329504529728574896890507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7029429967542931133664149 329504529728574896890507)
                  ·
                    rfl

theorem cell23_5775370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_5775370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775370 prefixEnd_5775370 := by exact prefixLift 5775370
  have htrace : WordTrace (prefixWord ++ tailWord_5775370) baseStart_5775370 baseEnd_5775370 := by
    simpa [prefixWord, tailWord_5775370, baseEnd_5775370] using wordTrace_append hprefix tailTrace_5775370
  have hstable : (prefixWord ++ tailWord_5775370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775370).length < 2 ^ (prefixWord ++ tailWord_5775370).sum := by decide
  have hdescent : baseEnd_5775370 < baseStart_5775370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775397 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 1, 1, 3]
def baseStart_5775397 : Nat := 118140960795 + 5775397 * 2 ^ 59
def prefixEnd_5775397 : Nat := 4983230072969 + 3 ^ 40 * 5775397 * 2
def baseEnd_5775397 : Nat := 2965554631534845466376939

theorem tailTrace_5775397 : CollatzResearch.WordTrace tailWord_5775397 prefixEnd_5775397 2965554631534845466376939 := by
  unfold tailWord_5775397
  simp only [CollatzResearch.WordTrace]
  refine ⟨210646033857730503124636445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140430689238487002083090963 210646033857730503124636445)
  ·
    refine ⟨78992262696648938671738667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210646033857730503124636445 78992262696648938671738667)
    ·
      refine ⟨118488394044973408007608001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78992262696648938671738667 118488394044973408007608001)
      ·
        refine ⟨88866295533730056005706001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118488394044973408007608001 88866295533730056005706001)
        ·
          refine ⟨66649721650297542004279501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88866295533730056005706001 66649721650297542004279501)
          ·
            refine ⟨24993645618861578251604813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66649721650297542004279501 24993645618861578251604813)
            ·
              refine ⟨9372617107073091844351805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24993645618861578251604813 9372617107073091844351805)
              ·
                refine ⟨3514731415152409441631927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9372617107073091844351805 3514731415152409441631927)
                ·
                  refine ⟨5272097122728614162447891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514731415152409441631927 5272097122728614162447891)
                  ·
                    refine ⟨7908145684092921243671837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5272097122728614162447891 7908145684092921243671837)
                    ·
                      refine ⟨2965554631534845466376939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7908145684092921243671837 2965554631534845466376939)
                      ·
                        rfl

theorem cell23_5775397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_5775397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775397 prefixEnd_5775397 := by exact prefixLift 5775397
  have htrace : WordTrace (prefixWord ++ tailWord_5775397) baseStart_5775397 baseEnd_5775397 := by
    simpa [prefixWord, tailWord_5775397, baseEnd_5775397] using wordTrace_append hprefix tailTrace_5775397
  have hstable : (prefixWord ++ tailWord_5775397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775397).length < 2 ^ (prefixWord ++ tailWord_5775397).sum := by decide
  have hdescent : baseEnd_5775397 < baseStart_5775397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775413 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5775413 : Nat := 118140960795 + 5775413 * 2 ^ 59
def prefixEnd_5775413 : Nat := 4983230072969 + 3 ^ 40 * 5775413 * 2
def baseEnd_5775413 : Nat := 988520949075105801258955

theorem tailTrace_5775413 : CollatzResearch.WordTrace tailWord_5775413 prefixEnd_5775413 988520949075105801258955 := by
  unfold tailWord_5775413
  simp only [CollatzResearch.WordTrace]
  refine ⟨210646617425672537857218893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140431078283781691904812595 210646617425672537857218893)
  ·
    refine ⟨78992481534627201696457085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210646617425672537857218893 78992481534627201696457085)
    ·
      refine ⟨29622180575485200636171407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78992481534627201696457085 29622180575485200636171407)
      ·
        refine ⟨44433270863227800954257111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29622180575485200636171407 44433270863227800954257111)
        ·
          refine ⟨66649906294841701431385667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44433270863227800954257111 66649906294841701431385667)
          ·
            refine ⟨99974859442262552147078501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66649906294841701431385667 99974859442262552147078501)
            ·
              refine ⟨18745286145424228527577219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99974859442262552147078501 18745286145424228527577219)
              ·
                refine ⟨28117929218136342791365829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18745286145424228527577219 28117929218136342791365829)
                ·
                  refine ⟨5272111728400564273381093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28117929218136342791365829 5272111728400564273381093)
                  ·
                    refine ⟨988520949075105801258955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272111728400564273381093 988520949075105801258955)
                    ·
                      rfl

theorem cell23_5775413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5775413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775413 prefixEnd_5775413 := by exact prefixLift 5775413
  have htrace : WordTrace (prefixWord ++ tailWord_5775413) baseStart_5775413 baseEnd_5775413 := by
    simpa [prefixWord, tailWord_5775413, baseEnd_5775413] using wordTrace_append hprefix tailTrace_5775413
  have hstable : (prefixWord ++ tailWord_5775413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775413).length < 2 ^ (prefixWord ++ tailWord_5775413).sum := by decide
  have hdescent : baseEnd_5775413 < baseStart_5775413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775430 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5775430 : Nat := 118140960795 + 5775430 * 2 ^ 59
def prefixEnd_5775430 : Nat := 4983230072969 + 3 ^ 40 * 5775430 * 2
def baseEnd_5775430 : Nat := 988523858798814612421429

theorem tailTrace_5775430 : CollatzResearch.WordTrace tailWord_5775430 prefixEnd_5775430 988523858798814612421429 := by
  unfold tailWord_5775430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582726170831592180018367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140431491644407299840391829 6582726170831592180018367)
  ·
    refine ⟨9874089256247388270027551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582726170831592180018367 9874089256247388270027551)
    ·
      refine ⟨14811133884371082405041327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874089256247388270027551 14811133884371082405041327)
      ·
        refine ⟨22216700826556623607561991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811133884371082405041327 22216700826556623607561991)
        ·
          refine ⟨33325051239834935411342987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22216700826556623607561991 33325051239834935411342987)
          ·
            refine ⟨49987576859752403117014481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33325051239834935411342987 49987576859752403117014481)
            ·
              refine ⟨37490682644814302337760861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49987576859752403117014481 37490682644814302337760861)
              ·
                refine ⟨14059005991805363376660323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37490682644814302337760861 14059005991805363376660323)
                ·
                  refine ⟨21088508987708045064990485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14059005991805363376660323 21088508987708045064990485)
                  ·
                    refine ⟨988523858798814612421429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21088508987708045064990485 988523858798814612421429)
                    ·
                      rfl

theorem cell23_5775430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5775430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775430 prefixEnd_5775430 := by exact prefixLift 5775430
  have htrace : WordTrace (prefixWord ++ tailWord_5775430) baseStart_5775430 baseEnd_5775430 := by
    simpa [prefixWord, tailWord_5775430, baseEnd_5775430] using wordTrace_append hprefix tailTrace_5775430
  have hstable : (prefixWord ++ tailWord_5775430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775430).length < 2 ^ (prefixWord ++ tailWord_5775430).sum := by decide
  have hdescent : baseEnd_5775430 < baseStart_5775430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775437 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_5775437 : Nat := 118140960795 + 5775437 * 2 ^ 59
def prefixEnd_5775437 : Nat := 4983230072969 + 3 ^ 40 * 5775437 * 2
def baseEnd_5775437 : Nat := 2965575170761025309876755

theorem tailTrace_5775437 : CollatzResearch.WordTrace tailWord_5775437 prefixEnd_5775437 2965575170761025309876755 := by
  unfold tailWord_5775437
  simp only [CollatzResearch.WordTrace]
  refine ⟨210647492777585589956092565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140431661851723726637395043 210647492777585589956092565)
  ·
    refine ⟨9874101223949324529191839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 210647492777585589956092565 9874101223949324529191839)
    ·
      refine ⟨14811151835923986793787759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874101223949324529191839 14811151835923986793787759)
      ·
        refine ⟨22216727753885980190681639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811151835923986793787759 22216727753885980190681639)
        ·
          refine ⟨33325091630828970286022459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22216727753885980190681639 33325091630828970286022459)
          ·
            refine ⟨49987637446243455429033689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33325091630828970286022459 49987637446243455429033689)
            ·
              refine ⟨37490728084682591571775267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49987637446243455429033689 37490728084682591571775267)
              ·
                refine ⟨56236092127023887357662901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37490728084682591571775267 56236092127023887357662901)
                ·
                  refine ⟨5272133636908489439780897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56236092127023887357662901 5272133636908489439780897)
                  ·
                    refine ⟨3954100227681367079835673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272133636908489439780897 3954100227681367079835673)
                    ·
                      refine ⟨2965575170761025309876755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954100227681367079835673 2965575170761025309876755)
                      ·
                        rfl

theorem cell23_5775437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_5775437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775437 prefixEnd_5775437 := by exact prefixLift 5775437
  have htrace : WordTrace (prefixWord ++ tailWord_5775437) baseStart_5775437 baseEnd_5775437 := by
    simpa [prefixWord, tailWord_5775437, baseEnd_5775437] using wordTrace_append hprefix tailTrace_5775437
  have hstable : (prefixWord ++ tailWord_5775437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775437).length < 2 ^ (prefixWord ++ tailWord_5775437).sum := by decide
  have hdescent : baseEnd_5775437 < baseStart_5775437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775471 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 1, 2, 2]
def baseStart_5775471 : Nat := 118140960795 + 5775471 * 2 ^ 59
def prefixEnd_5775471 : Nat := 4983230072969 + 3 ^ 40 * 5775471 * 2
def baseEnd_5775471 : Nat := 2965592629103278176851599

theorem tailTrace_5775471 : CollatzResearch.WordTrace tailWord_5775471 prefixEnd_5775471 2965592629103278176851599 := by
  unfold tailWord_5775471
  simp only [CollatzResearch.WordTrace]
  refine ⟨210648732859462413762830267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140432488572974942508553511 210648732859462413762830267)
  ·
    refine ⟨315973099289193620644245401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210648732859462413762830267 315973099289193620644245401)
    ·
      refine ⟨236979824466895215483184051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 315973099289193620644245401 236979824466895215483184051)
      ·
        refine ⟨355469736700342823224776077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236979824466895215483184051 355469736700342823224776077)
        ·
          refine ⟨133301151262628558709291029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355469736700342823224776077 133301151262628558709291029)
          ·
            refine ⟨6248491465435713689498017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133301151262628558709291029 6248491465435713689498017)
            ·
              refine ⟨4686368599076785267123513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248491465435713689498017 4686368599076785267123513)
              ·
                refine ⟨3514776449307588950342635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686368599076785267123513 3514776449307588950342635)
                ·
                  refine ⟨5272164673961383425513953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514776449307588950342635 5272164673961383425513953)
                  ·
                    refine ⟨3954123505471037569135465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272164673961383425513953 3954123505471037569135465)
                    ·
                      refine ⟨2965592629103278176851599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954123505471037569135465 2965592629103278176851599)
                      ·
                        rfl

theorem cell23_5775471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 2, 2].length) (baseStart_5775471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775471 prefixEnd_5775471 := by exact prefixLift 5775471
  have htrace : WordTrace (prefixWord ++ tailWord_5775471) baseStart_5775471 baseEnd_5775471 := by
    simpa [prefixWord, tailWord_5775471, baseEnd_5775471] using wordTrace_append hprefix tailTrace_5775471
  have hstable : (prefixWord ++ tailWord_5775471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775471).length < 2 ^ (prefixWord ++ tailWord_5775471).sum := by decide
  have hdescent : baseEnd_5775471 < baseStart_5775471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775508 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5775508 : Nat := 118140960795 + 5775508 * 2 ^ 59
def prefixEnd_5775508 : Nat := 4983230072969 + 3 ^ 40 * 5775508 * 2
def baseEnd_5775508 : Nat := 2965611627887494532088929

theorem tailTrace_5775508 : CollatzResearch.WordTrace tailWord_5775508 prefixEnd_5775508 2965611627887494532088929 := by
  unfold tailWord_5775508
  simp only [CollatzResearch.WordTrace]
  refine ⟨105325041180164184540963589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140433388240218912721284785 105325041180164184540963589)
  ·
    refine ⟨19748445221280784601430673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105325041180164184540963589 19748445221280784601430673)
    ·
      refine ⟨14811333915960588451073005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19748445221280784601430673 14811333915960588451073005)
      ·
        refine ⟨5554250218485220669152377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14811333915960588451073005 5554250218485220669152377)
        ·
          refine ⟨4165687663863915501864283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5554250218485220669152377 4165687663863915501864283)
          ·
            refine ⟨6248531495795873252796425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165687663863915501864283 6248531495795873252796425)
            ·
              refine ⟨4686398621846904939597319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6248531495795873252796425 4686398621846904939597319)
              ·
                refine ⟨7029597932770357409395979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686398621846904939597319 7029597932770357409395979)
                ·
                  refine ⟨10544396899155536114093969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029597932770357409395979 10544396899155536114093969)
                  ·
                    refine ⟨7908297674366652085570477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10544396899155536114093969 7908297674366652085570477)
                    ·
                      refine ⟨2965611627887494532088929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7908297674366652085570477 2965611627887494532088929)
                      ·
                        rfl

theorem cell23_5775508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5775508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775508 prefixEnd_5775508 := by exact prefixLift 5775508
  have htrace : WordTrace (prefixWord ++ tailWord_5775508) baseStart_5775508 baseEnd_5775508 := by
    simpa [prefixWord, tailWord_5775508, baseEnd_5775508] using wordTrace_append hprefix tailTrace_5775508
  have hstable : (prefixWord ++ tailWord_5775508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775508).length < 2 ^ (prefixWord ++ tailWord_5775508).sum := by decide
  have hdescent : baseEnd_5775508 < baseStart_5775508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775514 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5775514 : Nat := 118140960795 + 5775514 * 2 ^ 59
def prefixEnd_5775514 : Nat := 4983230072969 + 3 ^ 40 * 5775514 * 2
def baseEnd_5775514 : Nat := 2965614708771421508613901

theorem tailTrace_5775514 : CollatzResearch.WordTrace tailWord_5775514 prefixEnd_5775514 2965614708771421508613901 := by
  unfold tailWord_5775514
  simp only [CollatzResearch.WordTrace]
  refine ⟨52662575299576658026661399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140433534132204421404430397 52662575299576658026661399)
  ·
    refine ⟨78993862949364987039992099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52662575299576658026661399 78993862949364987039992099)
    ·
      refine ⟨118490794424047480559988149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78993862949364987039992099 118490794424047480559988149)
      ·
        refine ⟨11108511977254451302498889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118490794424047480559988149 11108511977254451302498889)
        ·
          refine ⟨8331383982940838476874167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11108511977254451302498889 8331383982940838476874167)
          ·
            refine ⟨12497075974411257715311251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331383982940838476874167 12497075974411257715311251)
            ·
              refine ⟨18745613961616886572966877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497075974411257715311251 18745613961616886572966877)
              ·
                refine ⟨7029605235606332464862579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18745613961616886572966877 7029605235606332464862579)
                ·
                  refine ⟨10544407853409498697293869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029605235606332464862579 10544407853409498697293869)
                  ·
                    refine ⟨3954152945028562011485201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10544407853409498697293869 3954152945028562011485201)
                    ·
                      refine ⟨2965614708771421508613901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954152945028562011485201 2965614708771421508613901)
                      ·
                        rfl

theorem cell23_5775514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5775514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775514 prefixEnd_5775514 := by exact prefixLift 5775514
  have htrace : WordTrace (prefixWord ++ tailWord_5775514) baseStart_5775514 baseEnd_5775514 := by
    simpa [prefixWord, tailWord_5775514, baseEnd_5775514] using wordTrace_append hprefix tailTrace_5775514
  have hstable : (prefixWord ++ tailWord_5775514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775514).length < 2 ^ (prefixWord ++ tailWord_5775514).sum := by decide
  have hdescent : baseEnd_5775514 < baseStart_5775514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775536 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_5775536 : Nat := 118140960795 + 5775536 * 2 ^ 59
def prefixEnd_5775536 : Nat := 4983230072969 + 3 ^ 40 * 5775536 * 2
def baseEnd_5775536 : Nat := 2965626005345820422538799

theorem tailTrace_5775536 : CollatzResearch.WordTrace tailWord_5775536 prefixEnd_5775536 2965626005345820422538799 := by
  unfold tailWord_5775536
  simp only [CollatzResearch.WordTrace]
  refine ⟨105325551802113464931973231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140434069069484619909297641 105325551802113464931973231)
  ·
    refine ⟨157988327703170197397959847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105325551802113464931973231 157988327703170197397959847)
    ·
      refine ⟨236982491554755296096939771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157988327703170197397959847 236982491554755296096939771)
      ·
        refine ⟨355473737332132944145409657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236982491554755296096939771 355473737332132944145409657)
        ·
          refine ⟨266605302999099708109057243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355473737332132944145409657 266605302999099708109057243)
          ·
            refine ⟨399907954498649562163585865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266605302999099708109057243 399907954498649562163585865)
            ·
              refine ⟨299930965873987171622689399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399907954498649562163585865 299930965873987171622689399)
              ·
                refine ⟨449896448810980757434034099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299930965873987171622689399 449896448810980757434034099)
                ·
                  refine ⟨674844673216471136151051149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449896448810980757434034099 674844673216471136151051149)
                  ·
                    refine ⟨253066752456176676056644181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674844673216471136151051149 253066752456176676056644181)
                    ·
                      refine ⟨2965626005345820422538799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253066752456176676056644181 2965626005345820422538799)
                      ·
                        rfl

theorem cell23_5775536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_5775536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775536 prefixEnd_5775536 := by exact prefixLift 5775536
  have htrace : WordTrace (prefixWord ++ tailWord_5775536) baseStart_5775536 baseEnd_5775536 := by
    simpa [prefixWord, tailWord_5775536, baseEnd_5775536] using wordTrace_append hprefix tailTrace_5775536
  have hstable : (prefixWord ++ tailWord_5775536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775536).length < 2 ^ (prefixWord ++ tailWord_5775536).sum := by decide
  have hdescent : baseEnd_5775536 < baseStart_5775536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775544 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2]
def baseStart_5775544 : Nat := 118140960795 + 5775544 * 2 ^ 59
def prefixEnd_5775544 : Nat := 4983230072969 + 3 ^ 40 * 5775544 * 2
def baseEnd_5775544 : Nat := 2965630113191056391238763

theorem tailTrace_5775544 : CollatzResearch.WordTrace tailWord_5775544 prefixEnd_5775544 2965630113191056391238763 := by
  unfold tailWord_5775544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105325697694098973615118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140434263592131964820158457 105325697694098973615118843)
  ·
    refine ⟨157988546541148460422678265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105325697694098973615118843 157988546541148460422678265)
    ·
      refine ⟨118491409905861345317008699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157988546541148460422678265 118491409905861345317008699)
      ·
        refine ⟨177737114858792017975513049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118491409905861345317008699 177737114858792017975513049)
        ·
          refine ⟨133302836144094013481634787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177737114858792017975513049 133302836144094013481634787)
          ·
            refine ⟨199954254216141020222452181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133302836144094013481634787 199954254216141020222452181)
            ·
              refine ⟨4686427833190805161463723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 199954254216141020222452181 4686427833190805161463723)
              ·
                refine ⟨7029641749786207742195585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686427833190805161463723 7029641749786207742195585)
                ·
                  refine ⟨5272231312339655806646689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7029641749786207742195585 5272231312339655806646689)
                  ·
                    refine ⟨3954173484254741854985017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272231312339655806646689 3954173484254741854985017)
                    ·
                      refine ⟨2965630113191056391238763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954173484254741854985017 2965630113191056391238763)
                      ·
                        rfl

theorem cell23_5775544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_5775544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775544 prefixEnd_5775544 := by exact prefixLift 5775544
  have htrace : WordTrace (prefixWord ++ tailWord_5775544) baseStart_5775544 baseEnd_5775544 := by
    simpa [prefixWord, tailWord_5775544, baseEnd_5775544] using wordTrace_append hprefix tailTrace_5775544
  have hstable : (prefixWord ++ tailWord_5775544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775544).length < 2 ^ (prefixWord ++ tailWord_5775544).sum := by decide
  have hdescent : baseEnd_5775544 < baseStart_5775544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775563 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 2, 5]
def baseStart_5775563 : Nat := 118140960795 + 5775563 * 2 ^ 59
def prefixEnd_5775563 : Nat := 4983230072969 + 3 ^ 40 * 5775563 * 2
def baseEnd_5775563 : Nat := 988546623107830605633725

theorem tailTrace_5775563 : CollatzResearch.WordTrace tailWord_5775563 prefixEnd_5775563 988546623107830605633725 := by
  unfold tailWord_5775563
  simp only [CollatzResearch.WordTrace]
  refine ⟨210652088375129113475179343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140434725583419408983452895 210652088375129113475179343)
  ·
    refine ⟨315978132562693670212769015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210652088375129113475179343 315978132562693670212769015)
    ·
      refine ⟨473967198844040505319153523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315978132562693670212769015 473967198844040505319153523)
      ·
        refine ⟨710950798266060757978730285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473967198844040505319153523 710950798266060757978730285)
        ·
          refine ⟨266606549349772784242023857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 710950798266060757978730285 266606549349772784242023857)
          ·
            refine ⟨199954912012329588181517893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266606549349772784242023857 199954912012329588181517893)
            ·
              refine ⟨37491546002311797784034605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 199954912012329588181517893 37491546002311797784034605)
              ·
                refine ⟨14059329750866924169012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37491546002311797784034605 14059329750866924169012977)
                ·
                  refine ⟨10544497313150193126759733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14059329750866924169012977 10544497313150193126759733)
                  ·
                    refine ⟨988546623107830605633725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10544497313150193126759733 988546623107830605633725)
                    ·
                      rfl

theorem cell23_5775563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 5].length) (baseStart_5775563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775563 prefixEnd_5775563 := by exact prefixLift 5775563
  have htrace : WordTrace (prefixWord ++ tailWord_5775563) baseStart_5775563 baseEnd_5775563 := by
    simpa [prefixWord, tailWord_5775563, baseEnd_5775563] using wordTrace_append hprefix tailTrace_5775563
  have hstable : (prefixWord ++ tailWord_5775563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775563).length < 2 ^ (prefixWord ++ tailWord_5775563).sum := by decide
  have hdescent : baseEnd_5775563 < baseStart_5775563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775600 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2]
def baseStart_5775600 : Nat := 118140960795 + 5775600 * 2 ^ 59
def prefixEnd_5775600 : Nat := 4983230072969 + 3 ^ 40 * 5775600 * 2
def baseEnd_5775600 : Nat := 2965658868107708172138505

theorem tailTrace_5775600 : CollatzResearch.WordTrace tailWord_5775600 prefixEnd_5775600 2965658868107708172138505 := by
  unfold tailWord_5775600
  simp only [CollatzResearch.WordTrace]
  refine ⟨105326718937997534397138127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140435625250663379196184169 105326718937997534397138127)
  ·
    refine ⟨157990078406996301595707191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105326718937997534397138127 157990078406996301595707191)
    ·
      refine ⟨236985117610494452393560787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157990078406996301595707191 236985117610494452393560787)
      ·
        refine ⟨355477676415741678590341181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236985117610494452393560787 355477676415741678590341181)
        ·
          refine ⟨133304128655903129471377943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355477676415741678590341181 133304128655903129471377943)
          ·
            refine ⟨199956192983854694207066915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133304128655903129471377943 199956192983854694207066915)
            ·
              refine ⟨299934289475782041310600373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199956192983854694207066915 299934289475782041310600373)
              ·
                refine ⟨28118839638354566372868785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 299934289475782041310600373 28118839638354566372868785)
                ·
                  refine ⟨21089129728765924779651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28118839638354566372868785 21089129728765924779651589)
                  ·
                    refine ⟨3954211824143610896184673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21089129728765924779651589 3954211824143610896184673)
                    ·
                      refine ⟨2965658868107708172138505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954211824143610896184673 2965658868107708172138505)
                      ·
                        rfl

theorem cell23_5775600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 4, 2].length) (baseStart_5775600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775600 prefixEnd_5775600 := by exact prefixLift 5775600
  have htrace : WordTrace (prefixWord ++ tailWord_5775600) baseStart_5775600 baseEnd_5775600 := by
    simpa [prefixWord, tailWord_5775600, baseEnd_5775600] using wordTrace_append hprefix tailTrace_5775600
  have hstable : (prefixWord ++ tailWord_5775600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775600).length < 2 ^ (prefixWord ++ tailWord_5775600).sum := by decide
  have hdescent : baseEnd_5775600 < baseStart_5775600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775613 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_5775613 : Nat := 118140960795 + 5775613 * 2 ^ 59
def prefixEnd_5775613 : Nat := 4983230072969 + 3 ^ 40 * 5775613 * 2
def baseEnd_5775613 : Nat := 2965665543356216621275945

theorem tailTrace_5775613 : CollatzResearch.WordTrace tailWord_5775613 prefixEnd_5775613 2965665543356216621275945 := by
  unfold tailWord_5775613
  simp only [CollatzResearch.WordTrace]
  refine ⟨210653912024947972014499493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140435941349965314676332995 210653912024947972014499493)
  ·
    refine ⟨39497608504677744752718655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210653912024947972014499493 39497608504677744752718655)
    ·
      refine ⟨59246412757016617129077983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39497608504677744752718655 59246412757016617129077983)
      ·
        refine ⟨88869619135524925693616975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59246412757016617129077983 88869619135524925693616975)
        ·
          refine ⟨133304428703287388540425463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88869619135524925693616975 133304428703287388540425463)
          ·
            refine ⟨199956643054931082810638195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133304428703287388540425463 199956643054931082810638195)
            ·
              refine ⟨299934964582396624215957293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199956643054931082810638195 299934964582396624215957293)
              ·
                refine ⟨112475611718398734080983985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299934964582396624215957293 112475611718398734080983985)
                ·
                  refine ⟨84356708788799050560737989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112475611718398734080983985 84356708788799050560737989)
                  ·
                    refine ⟨15816882897899821980138373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84356708788799050560737989 15816882897899821980138373)
                    ·
                      refine ⟨2965665543356216621275945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15816882897899821980138373 2965665543356216621275945)
                      ·
                        rfl

theorem cell23_5775613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_5775613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775613 prefixEnd_5775613 := by exact prefixLift 5775613
  have htrace : WordTrace (prefixWord ++ tailWord_5775613) baseStart_5775613 baseEnd_5775613 := by
    simpa [prefixWord, tailWord_5775613, baseEnd_5775613] using wordTrace_append hprefix tailTrace_5775613
  have hstable : (prefixWord ++ tailWord_5775613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775613).length < 2 ^ (prefixWord ++ tailWord_5775613).sum := by decide
  have hdescent : baseEnd_5775613 < baseStart_5775613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775627 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 1, 4]
def baseStart_5775627 : Nat := 118140960795 + 5775627 * 2 ^ 59
def prefixEnd_5775627 : Nat := 4983230072969 + 3 ^ 40 * 5775627 * 2
def baseEnd_5775627 : Nat := 988557577361793188833627

theorem tailTrace_5775627 : CollatzResearch.WordTrace tailWord_5775627 prefixEnd_5775627 988557577361793188833627 := by
  unfold tailWord_5775627
  simp only [CollatzResearch.WordTrace]
  refine ⟨210654422646897252405509135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140436281764598168270339423 210654422646897252405509135)
  ·
    refine ⟨315981633970345878608263703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210654422646897252405509135 315981633970345878608263703)
    ·
      refine ⟨473972450955518817912395555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315981633970345878608263703 473972450955518817912395555)
      ·
        refine ⟨710958676433278226868593333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473972450955518817912395555 710958676433278226868593333)
        ·
          refine ⟨66652375915619833768930625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 710958676433278226868593333 66652375915619833768930625)
          ·
            refine ⟨49989281936714875326697969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66652375915619833768930625 49989281936714875326697969)
            ·
              refine ⟨37491961452536156495023477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49989281936714875326697969 37491961452536156495023477)
              ·
                refine ⟨3514871386175264671408451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37491961452536156495023477 3514871386175264671408451)
                ·
                  refine ⟨5272307079262897007112677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514871386175264671408451 5272307079262897007112677)
                  ·
                    refine ⟨988557577361793188833627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272307079262897007112677 988557577361793188833627)
                    ·
                      rfl

theorem cell23_5775627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 1, 4].length) (baseStart_5775627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775627 prefixEnd_5775627 := by exact prefixLift 5775627
  have htrace : WordTrace (prefixWord ++ tailWord_5775627) baseStart_5775627 baseEnd_5775627 := by
    simpa [prefixWord, tailWord_5775627, baseEnd_5775627] using wordTrace_append hprefix tailTrace_5775627
  have hstable : (prefixWord ++ tailWord_5775627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775627).length < 2 ^ (prefixWord ++ tailWord_5775627).sum := by decide
  have hdescent : baseEnd_5775627 < baseStart_5775627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775640 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 6]
def baseStart_5775640 : Nat := 118140960795 + 5775640 * 2 ^ 59
def prefixEnd_5775640 : Nat := 4983230072969 + 3 ^ 40 * 5775640 * 2
def baseEnd_5775640 : Nat := 329519934148209779515369

theorem tailTrace_5775640 : CollatzResearch.WordTrace tailWord_5775640 prefixEnd_5775640 329519934148209779515369 := by
  unfold tailWord_5775640
  simp only [CollatzResearch.WordTrace]
  refine ⟨105327448397925077812866187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140436597863900103750488249 105327448397925077812866187)
  ·
    refine ⟨157991172596887616719299281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105327448397925077812866187 157991172596887616719299281)
    ·
      refine ⟨118493379447665712539474461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157991172596887616719299281 118493379447665712539474461)
      ·
        refine ⟨44435017292874642202302923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118493379447665712539474461 44435017292874642202302923)
        ·
          refine ⟨66652525939311963303454385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44435017292874642202302923 66652525939311963303454385)
          ·
            refine ⟨49989394454483972477590789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66652525939311963303454385 49989394454483972477590789)
            ·
              refine ⟨9373011460215744839548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49989394454483972477590789 9373011460215744839548273)
              ·
                refine ⟨7029758595161808629661205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9373011460215744839548273 7029758595161808629661205)
                ·
                  refine ⟨329519934148209779515369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7029758595161808629661205 329519934148209779515369)
                  ·
                    rfl

theorem cell23_5775640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 6].length) (baseStart_5775640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775640 prefixEnd_5775640 := by exact prefixLift 5775640
  have htrace : WordTrace (prefixWord ++ tailWord_5775640) baseStart_5775640 baseEnd_5775640 := by
    simpa [prefixWord, tailWord_5775640, baseEnd_5775640] using wordTrace_append hprefix tailTrace_5775640
  have hstable : (prefixWord ++ tailWord_5775640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775640).length < 2 ^ (prefixWord ++ tailWord_5775640).sum := by decide
  have hdescent : baseEnd_5775640 < baseStart_5775640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775667 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 3]
def baseStart_5775667 : Nat := 118140960795 + 5775667 * 2 ^ 59
def prefixEnd_5775667 : Nat := 4983230072969 + 3 ^ 40 * 5775667 * 2
def baseEnd_5775667 : Nat := 2965693271311559410000697

theorem tailTrace_5775667 : CollatzResearch.WordTrace tailWord_5775667 prefixEnd_5775667 2965693271311559410000697 := by
  unfold tailWord_5775667
  simp only [CollatzResearch.WordTrace]
  refine ⟨210655881566752339236965255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140437254377834892824643503 210655881566752339236965255)
  ·
    refine ⟨315983822350128508855447883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210655881566752339236965255 315983822350128508855447883)
    ·
      refine ⟨473975733525192763283171825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315983822350128508855447883 473975733525192763283171825)
      ·
        refine ⟨355481800143894572462378869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473975733525192763283171825 355481800143894572462378869)
        ·
          refine ⟨33326418763490116168348019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 355481800143894572462378869 33326418763490116168348019)
          ·
            refine ⟨49989628145235174252522029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33326418763490116168348019 49989628145235174252522029)
            ·
              refine ⟨18746110554463190344695761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49989628145235174252522029 18746110554463190344695761)
              ·
                refine ⟨14059582915847392758521821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18746110554463190344695761 14059582915847392758521821)
                ·
                  refine ⟨5272343593442772284445683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14059582915847392758521821 5272343593442772284445683)
                  ·
                    refine ⟨7908515390164158426668525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5272343593442772284445683 7908515390164158426668525)
                    ·
                      refine ⟨2965693271311559410000697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7908515390164158426668525 2965693271311559410000697)
                      ·
                        rfl

theorem cell23_5775667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 3].length) (baseStart_5775667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775667 prefixEnd_5775667 := by exact prefixLift 5775667
  have htrace : WordTrace (prefixWord ++ tailWord_5775667) baseStart_5775667 baseEnd_5775667 := by
    simpa [prefixWord, tailWord_5775667, baseEnd_5775667] using wordTrace_append hprefix tailTrace_5775667
  have hstable : (prefixWord ++ tailWord_5775667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775667).length < 2 ^ (prefixWord ++ tailWord_5775667).sum := by decide
  have hdescent : baseEnd_5775667 < baseStart_5775667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775717 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_5775717 : Nat := 118140960795 + 5775717 * 2 ^ 59
def prefixEnd_5775717 : Nat := 4983230072969 + 3 ^ 40 * 5775717 * 2
def baseEnd_5775717 : Nat := 988572981781428071458489

theorem tailTrace_5775717 : CollatzResearch.WordTrace tailWord_5775717 prefixEnd_5775717 988572981781428071458489 := by
  unfold tailWord_5775717
  simp only [CollatzResearch.WordTrace]
  refine ⟨210657705216571197776285405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140438470144380798517523603 210657705216571197776285405)
  ·
    refine ⟨78996639456214199166107027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210657705216571197776285405 78996639456214199166107027)
    ·
      refine ⟨118494959184321298749160541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78996639456214199166107027 118494959184321298749160541)
      ·
        refine ⟨44435609694120487030935203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118494959184321298749160541 44435609694120487030935203)
        ·
          refine ⟨66653414541180730546402805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44435609694120487030935203 66653414541180730546402805)
          ·
            refine ⟨6248757613235693488725263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66653414541180730546402805 6248757613235693488725263)
            ·
              refine ⟨9373136419853540233087895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248757613235693488725263 9373136419853540233087895)
              ·
                refine ⟨14059704629780310349631843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373136419853540233087895 14059704629780310349631843)
                ·
                  refine ⟨21089556944670465524447765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14059704629780310349631843 21089556944670465524447765)
                  ·
                    refine ⟨988572981781428071458489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21089556944670465524447765 988572981781428071458489)
                    ·
                      rfl

theorem cell23_5775717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_5775717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775717 prefixEnd_5775717 := by exact prefixLift 5775717
  have htrace : WordTrace (prefixWord ++ tailWord_5775717) baseStart_5775717 baseEnd_5775717 := by
    simpa [prefixWord, tailWord_5775717, baseEnd_5775717] using wordTrace_append hprefix tailTrace_5775717
  have hstable : (prefixWord ++ tailWord_5775717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775717).length < 2 ^ (prefixWord ++ tailWord_5775717).sum := by decide
  have hdescent : baseEnd_5775717 < baseStart_5775717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775723 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_5775723 : Nat := 118140960795 + 5775723 * 2 ^ 59
def prefixEnd_5775723 : Nat := 4983230072969 + 3 ^ 40 * 5775723 * 2
def baseEnd_5775723 : Nat := 2965722026228211190900439

theorem tailTrace_5775723 : CollatzResearch.WordTrace tailWord_5775723 prefixEnd_5775723 2965722026228211190900439 := by
  unfold tailWord_5775723
  simp only [CollatzResearch.WordTrace]
  refine ⟨210657924054549460801003823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140438616036366307200669215 210657924054549460801003823)
  ·
    refine ⟨315986886081824191201505735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210657924054549460801003823 315986886081824191201505735)
    ·
      refine ⟨473980329122736286802258603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315986886081824191201505735 473980329122736286802258603)
      ·
        refine ⟨710970493684104430203387905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473980329122736286802258603 710970493684104430203387905)
        ·
          refine ⟨533227870263078322652540929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710970493684104430203387905 533227870263078322652540929)
          ·
            refine ⟨399920902697308741989405697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 533227870263078322652540929 399920902697308741989405697)
            ·
              refine ⟨299940677022981556492054273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399920902697308741989405697 299940677022981556492054273)
              ·
                refine ⟨224955507767236167369040705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299940677022981556492054273 224955507767236167369040705)
                ·
                  refine ⟨168716630825427125526780529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224955507767236167369040705 168716630825427125526780529)
                  ·
                    refine ⟨126537473119070344145085397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168716630825427125526780529 126537473119070344145085397)
                    ·
                      refine ⟨2965722026228211190900439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126537473119070344145085397 2965722026228211190900439)
                      ·
                        rfl

theorem cell23_5775723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_5775723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775723 prefixEnd_5775723 := by exact prefixLift 5775723
  have htrace : WordTrace (prefixWord ++ tailWord_5775723) baseStart_5775723 baseEnd_5775723 := by
    simpa [prefixWord, tailWord_5775723, baseEnd_5775723] using wordTrace_append hprefix tailTrace_5775723
  have hstable : (prefixWord ++ tailWord_5775723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775723).length < 2 ^ (prefixWord ++ tailWord_5775723).sum := by decide
  have hdescent : baseEnd_5775723 < baseStart_5775723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775724 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 4]
def baseStart_5775724 : Nat := 118140960795 + 5775724 * 2 ^ 59
def prefixEnd_5775724 : Nat := 4983230072969 + 3 ^ 40 * 5775724 * 2
def baseEnd_5775724 : Nat := 2965722539708865686987935

theorem tailTrace_5775724 : CollatzResearch.WordTrace tailWord_5775724 prefixEnd_5775724 2965722539708865686987935 := by
  unfold tailWord_5775724
  simp only [CollatzResearch.WordTrace]
  refine ⟨105328980263772918985895113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140438640351697225314526817 105328980263772918985895113)
  ·
    refine ⟨78996735197829689239421335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105328980263772918985895113 78996735197829689239421335)
    ·
      refine ⟨118495102796744533859132003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78996735197829689239421335 118495102796744533859132003)
      ·
        refine ⟨177742654195116800788698005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118495102796744533859132003 177742654195116800788698005)
        ·
          refine ⟨8331686915396100036970219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177742654195116800788698005 8331686915396100036970219)
          ·
            refine ⟨12497530373094150055455329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331686915396100036970219 12497530373094150055455329)
            ·
              refine ⟨9373147779820612541591497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497530373094150055455329 9373147779820612541591497)
              ·
                refine ⟨7029860834865459406193623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9373147779820612541591497 7029860834865459406193623)
                ·
                  refine ⟨10544791252298189109290435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029860834865459406193623 10544791252298189109290435)
                  ·
                    refine ⟨15817186878447283663935653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10544791252298189109290435 15817186878447283663935653)
                    ·
                      refine ⟨2965722539708865686987935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15817186878447283663935653 2965722539708865686987935)
                      ·
                        rfl

theorem cell23_5775724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_5775724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775724 prefixEnd_5775724 := by exact prefixLift 5775724
  have htrace : WordTrace (prefixWord ++ tailWord_5775724) baseStart_5775724 baseEnd_5775724 := by
    simpa [prefixWord, tailWord_5775724, baseEnd_5775724] using wordTrace_append hprefix tailTrace_5775724
  have hstable : (prefixWord ++ tailWord_5775724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775724).length < 2 ^ (prefixWord ++ tailWord_5775724).sum := by decide
  have hdescent : baseEnd_5775724 < baseStart_5775724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775730 : List Nat := [3, 2, 1, 2, 1, 4, 1, 9]
def baseStart_5775730 : Nat := 118140960795 + 5775730 * 2 ^ 59
def prefixEnd_5775730 : Nat := 4983230072969 + 3 ^ 40 * 5775730 * 2
def baseEnd_5775730 : Nat := 109841689651584913463441

theorem tailTrace_5775730 : CollatzResearch.WordTrace tailWord_5775730 prefixEnd_5775730 109841689651584913463441 := by
  unfold tailWord_5775730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52664544841381025249127161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140438786243682733997672429 52664544841381025249127161)
  ·
    refine ⟨39498408631035768936845371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52664544841381025249127161 39498408631035768936845371)
    ·
      refine ⟨59247612946553653405268057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39498408631035768936845371 59247612946553653405268057)
      ·
        refine ⟨44435709709915240053951043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59247612946553653405268057 44435709709915240053951043)
        ·
          refine ⟨66653564564872860080926565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44435709709915240053951043 66653564564872860080926565)
          ·
            refine ⟨12497543355913661265173731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66653564564872860080926565 12497543355913661265173731)
            ·
              refine ⟨18746315033870491897760597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12497543355913661265173731 18746315033870491897760597)
              ·
                refine ⟨109841689651584913463441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18746315033870491897760597 109841689651584913463441)
                ·
                  rfl

theorem cell23_5775730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_5775730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775730 prefixEnd_5775730 := by exact prefixLift 5775730
  have htrace : WordTrace (prefixWord ++ tailWord_5775730) baseStart_5775730 baseEnd_5775730 := by
    simpa [prefixWord, tailWord_5775730, baseEnd_5775730] using wordTrace_append hprefix tailTrace_5775730
  have hstable : (prefixWord ++ tailWord_5775730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775730).length < 2 ^ (prefixWord ++ tailWord_5775730).sum := by decide
  have hdescent : baseEnd_5775730 < baseStart_5775730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775747 : List Nat := [1, 1, 1, 3, 7, 1, 9]
def baseStart_5775747 : Nat := 118140960795 + 5775747 * 2 ^ 59
def prefixEnd_5775747 : Nat := 4983230072969 + 3 ^ 40 * 5775747 * 2
def baseEnd_5775747 : Nat := 36614004318073075271609

theorem tailTrace_5775747 : CollatzResearch.WordTrace tailWord_5775747 prefixEnd_5775747 36614004318073075271609 := by
  unfold tailWord_5775747
  simp only [CollatzResearch.WordTrace]
  refine ⟨210658799406462512899877495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140439199604308341933251663 210658799406462512899877495)
  ·
    refine ⟨315988199109693769349816243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210658799406462512899877495 315988199109693769349816243)
    ·
      refine ⟨473982298664540654024724365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 315988199109693769349816243 473982298664540654024724365)
      ·
        refine ⟨177743361999202745259271637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 473982298664540654024724365 177743361999202745259271637)
        ·
          refine ⟨4165860046856314342014179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177743361999202745259271637 4165860046856314342014179)
          ·
            refine ⟨6248790070284471513021269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165860046856314342014179 6248790070284471513021269)
            ·
              refine ⟨36614004318073075271609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6248790070284471513021269 36614004318073075271609)
              ·
                rfl

theorem cell23_5775747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 9].length) (baseStart_5775747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775747 prefixEnd_5775747 := by exact prefixLift 5775747
  have htrace : WordTrace (prefixWord ++ tailWord_5775747) baseStart_5775747 baseEnd_5775747 := by
    simpa [prefixWord, tailWord_5775747, baseEnd_5775747] using wordTrace_append hprefix tailTrace_5775747
  have hstable : (prefixWord ++ tailWord_5775747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775747).length < 2 ^ (prefixWord ++ tailWord_5775747).sum := by decide
  have hdescent : baseEnd_5775747 < baseStart_5775747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775758 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5775758 : Nat := 118140960795 + 5775758 * 2 ^ 59
def prefixEnd_5775758 : Nat := 4983230072969 + 3 ^ 40 * 5775758 * 2
def baseEnd_5775758 : Nat := 2965739998051118553962779

theorem tailTrace_5775758 : CollatzResearch.WordTrace tailWord_5775758 prefixEnd_5775758 2965739998051118553962779 := by
  unfold tailWord_5775758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26332400076177832722315991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140439467072948441185685285 26332400076177832722315991)
  ·
    refine ⟨39498600114266749083473987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26332400076177832722315991 39498600114266749083473987)
    ·
      refine ⟨59247900171400123625210981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39498600114266749083473987 59247900171400123625210981)
      ·
        refine ⟨11108981282137523179727059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59247900171400123625210981 11108981282137523179727059)
        ·
          refine ⟨16663471923206284769590589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108981282137523179727059 16663471923206284769590589)
          ·
            refine ⟨6248801971202356788596471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16663471923206284769590589 6248801971202356788596471)
            ·
              refine ⟨9373202956803535182894707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248801971202356788596471 9373202956803535182894707)
              ·
                refine ⟨14059804435205302774342061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373202956803535182894707 14059804435205302774342061)
                ·
                  refine ⟨5272426663201988540378273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14059804435205302774342061 5272426663201988540378273)
                  ·
                    refine ⟨3954319997401491405283705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272426663201988540378273 3954319997401491405283705)
                    ·
                      refine ⟨2965739998051118553962779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954319997401491405283705 2965739998051118553962779)
                      ·
                        rfl

theorem cell23_5775758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5775758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775758 prefixEnd_5775758 := by exact prefixLift 5775758
  have htrace : WordTrace (prefixWord ++ tailWord_5775758) baseStart_5775758 baseEnd_5775758 := by
    simpa [prefixWord, tailWord_5775758, baseEnd_5775758] using wordTrace_append hprefix tailTrace_5775758
  have hstable : (prefixWord ++ tailWord_5775758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775758).length < 2 ^ (prefixWord ++ tailWord_5775758).sum := by decide
  have hdescent : baseEnd_5775758 < baseStart_5775758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775837 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 7]
def baseStart_5775837 : Nat := 118140960795 + 5775837 * 2 ^ 59
def prefixEnd_5775837 : Nat := 4983230072969 + 3 ^ 40 * 5775837 * 2
def baseEnd_5775837 : Nat := 329531173669202638319435

theorem tailTrace_5775837 : CollatzResearch.WordTrace tailWord_5775837 prefixEnd_5775837 329531173669202638319435 := by
  unfold tailWord_5775837
  simp only [CollatzResearch.WordTrace]
  refine ⟨210662081976136458270653765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140441387984090972180435843 210662081976136458270653765)
  ·
    refine ⟨39499140370525585925747581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210662081976136458270653765 39499140370525585925747581)
    ·
      refine ⟨14812177638947094722155343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39499140370525585925747581 14812177638947094722155343)
      ·
        refine ⟨22218266458420642083233015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812177638947094722155343 22218266458420642083233015)
        ·
          refine ⟨33327399687630963124849523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218266458420642083233015 33327399687630963124849523)
          ·
            refine ⟨49991099531446444687274285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33327399687630963124849523 49991099531446444687274285)
            ·
              refine ⟨18746662324292416757727857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49991099531446444687274285 18746662324292416757727857)
              ·
                refine ⟨14059996743219312568295893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18746662324292416757727857 14059996743219312568295893)
                ·
                  refine ⟨329531173669202638319435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14059996743219312568295893 329531173669202638319435)
                  ·
                    rfl

theorem cell23_5775837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_5775837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775837 prefixEnd_5775837 := by exact prefixLift 5775837
  have htrace : WordTrace (prefixWord ++ tailWord_5775837) baseStart_5775837 baseEnd_5775837 := by
    simpa [prefixWord, tailWord_5775837, baseEnd_5775837] using wordTrace_append hprefix tailTrace_5775837
  have hstable : (prefixWord ++ tailWord_5775837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775837).length < 2 ^ (prefixWord ++ tailWord_5775837).sum := by decide
  have hdescent : baseEnd_5775837 < baseStart_5775837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775847 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5775847 : Nat := 118140960795 + 5775847 * 2 ^ 59
def prefixEnd_5775847 : Nat := 4983230072969 + 3 ^ 40 * 5775847 * 2
def baseEnd_5775847 : Nat := 2965785697829368705749869

theorem tailTrace_5775847 : CollatzResearch.WordTrace tailWord_5775847 prefixEnd_5775847 2965785697829368705749869 := by
  unfold tailWord_5775847
  simp only [CollatzResearch.WordTrace]
  refine ⟨210662446706100229978517795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140441631137400153319011863 210662446706100229978517795)
  ·
    refine ⟨315993670059150344967776693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210662446706100229978517795 315993670059150344967776693)
    ·
      refine ⟨29624406568045344840729065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 315993670059150344967776693 29624406568045344840729065)
      ·
        refine ⟨22218304926034008630546799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29624406568045344840729065 22218304926034008630546799)
        ·
          refine ⟨33327457389051012945820199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218304926034008630546799 33327457389051012945820199)
          ·
            refine ⟨49991186083576519418730299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33327457389051012945820199 49991186083576519418730299)
            ·
              refine ⟨74986779125364779128095449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49991186083576519418730299 74986779125364779128095449)
              ·
                refine ⟨56240084344023584346071587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74986779125364779128095449 56240084344023584346071587)
                ·
                  refine ⟨84360126516035376519107381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56240084344023584346071587 84360126516035376519107381)
                  ·
                    refine ⟨7908761860878316548666317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84360126516035376519107381 7908761860878316548666317)
                    ·
                      refine ⟨2965785697829368705749869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7908761860878316548666317 2965785697829368705749869)
                      ·
                        rfl

theorem cell23_5775847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5775847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775847 prefixEnd_5775847 := by exact prefixLift 5775847
  have htrace : WordTrace (prefixWord ++ tailWord_5775847) baseStart_5775847 baseEnd_5775847 := by
    simpa [prefixWord, tailWord_5775847, baseEnd_5775847] using wordTrace_append hprefix tailTrace_5775847
  have hstable : (prefixWord ++ tailWord_5775847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775847).length < 2 ^ (prefixWord ++ tailWord_5775847).sum := by decide
  have hdescent : baseEnd_5775847 < baseStart_5775847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775854 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_5775854 : Nat := 118140960795 + 5775854 * 2 ^ 59
def prefixEnd_5775854 : Nat := 4983230072969 + 3 ^ 40 * 5775854 * 2
def baseEnd_5775854 : Nat := 329532143577105575373593

theorem tailTrace_5775854 : CollatzResearch.WordTrace tailWord_5775854 prefixEnd_5775854 329532143577105575373593 := by
  unfold tailWord_5775854
  simp only [CollatzResearch.WordTrace]
  refine ⟨26332837752134358771752827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140441801344716580116015077 26332837752134358771752827)
  ·
    refine ⟨39499256628201538157629241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26332837752134358771752827 39499256628201538157629241)
    ·
      refine ⟨29624442471151153618221931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39499256628201538157629241 29624442471151153618221931)
      ·
        refine ⟨44436663706726730427332897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29624442471151153618221931 44436663706726730427332897)
        ·
          refine ⟨33327497780045047820499673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44436663706726730427332897 33327497780045047820499673)
          ·
            refine ⟨24995623335033785865374755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33327497780045047820499673 24995623335033785865374755)
            ·
              refine ⟨37493435002550678798062133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24995623335033785865374755 37493435002550678798062133)
              ·
                refine ⟨3515009531489126137318325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37493435002550678798062133 3515009531489126137318325)
                ·
                  refine ⟨329532143577105575373593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515009531489126137318325 329532143577105575373593)
                  ·
                    rfl

theorem cell23_5775854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_5775854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775854 prefixEnd_5775854 := by exact prefixLift 5775854
  have htrace : WordTrace (prefixWord ++ tailWord_5775854) baseStart_5775854 baseEnd_5775854 := by
    simpa [prefixWord, tailWord_5775854, baseEnd_5775854] using wordTrace_append hprefix tailTrace_5775854
  have hstable : (prefixWord ++ tailWord_5775854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775854).length < 2 ^ (prefixWord ++ tailWord_5775854).sum := by decide
  have hdescent : baseEnd_5775854 < baseStart_5775854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775878 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5775878 : Nat := 118140960795 + 5775878 * 2 ^ 59
def prefixEnd_5775878 : Nat := 4983230072969 + 3 ^ 40 * 5775878 * 2
def baseEnd_5775878 : Nat := 2965801615729658084462227

theorem tailTrace_5775878 : CollatzResearch.WordTrace tailWord_5775878 prefixEnd_5775878 2965801615729658084462227 := by
  unfold tailWord_5775878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583236792780872571028009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140442384912658614848597525 6583236792780872571028009)
  ·
    refine ⟨4937427594585654428271007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6583236792780872571028009 4937427594585654428271007)
    ·
      refine ⟨7406141391878481642406511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4937427594585654428271007 7406141391878481642406511)
      ·
        refine ⟨11109212087817722463609767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7406141391878481642406511 11109212087817722463609767)
        ·
          refine ⟨16663818131726583695414651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11109212087817722463609767 16663818131726583695414651)
          ·
            refine ⟨24995727197589875543121977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16663818131726583695414651 24995727197589875543121977)
            ·
              refine ⟨18746795398192406657341483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24995727197589875543121977 18746795398192406657341483)
              ·
                refine ⟨28120193097288609986012225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18746795398192406657341483 28120193097288609986012225)
                ·
                  refine ⟨21090144822966457489509169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28120193097288609986012225 21090144822966457489509169)
                  ·
                    refine ⟨15817608617224843117131877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21090144822966457489509169 15817608617224843117131877)
                    ·
                      refine ⟨2965801615729658084462227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15817608617224843117131877 2965801615729658084462227)
                      ·
                        rfl

theorem cell23_5775878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5775878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775878 prefixEnd_5775878 := by exact prefixLift 5775878
  have htrace : WordTrace (prefixWord ++ tailWord_5775878) baseStart_5775878 baseEnd_5775878 := by
    simpa [prefixWord, tailWord_5775878, baseEnd_5775878] using wordTrace_append hprefix tailTrace_5775878
  have hstable : (prefixWord ++ tailWord_5775878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775878).length < 2 ^ (prefixWord ++ tailWord_5775878).sum := by decide
  have hdescent : baseEnd_5775878 < baseStart_5775878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5775927 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 6]
def baseStart_5775927 : Nat := 118140960795 + 5775927 * 2 ^ 59
def prefixEnd_5775927 : Nat := 4983230072969 + 3 ^ 40 * 5775927 * 2
def baseEnd_5775927 : Nat := 329536308475747599194389

theorem tailTrace_5775927 : CollatzResearch.WordTrace tailWord_5775927 prefixEnd_5775927 329536308475747599194389 := by
  unfold tailWord_5775927
  simp only [CollatzResearch.WordTrace]
  refine ⟨210665364545810403641430035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140443576363873602427620023 210665364545810403641430035)
  ·
    refine ⟨315998046818715605462145053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210665364545810403641430035 315998046818715605462145053)
    ·
      refine ⟨118499267557018352048304395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315998046818715605462145053 118499267557018352048304395)
      ·
        refine ⟨177748901335527528072456593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118499267557018352048304395 177748901335527528072456593)
        ·
          refine ⟨133311676001645646054342445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177748901335527528072456593 133311676001645646054342445)
          ·
            refine ⟨49991878500617117270378417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133311676001645646054342445 49991878500617117270378417)
            ·
              refine ⟨37493908875462837952783813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49991878500617117270378417 37493908875462837952783813)
              ·
                refine ⟨7030107914149282116146965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37493908875462837952783813 7030107914149282116146965)
                ·
                  refine ⟨329536308475747599194389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7030107914149282116146965 329536308475747599194389)
                  ·
                    rfl

theorem cell23_5775927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 6].length) (baseStart_5775927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5775927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5775927 prefixEnd_5775927 := by exact prefixLift 5775927
  have htrace : WordTrace (prefixWord ++ tailWord_5775927) baseStart_5775927 baseEnd_5775927 := by
    simpa [prefixWord, tailWord_5775927, baseEnd_5775927] using wordTrace_append hprefix tailTrace_5775927
  have hstable : (prefixWord ++ tailWord_5775927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5775927).length < 2 ^ (prefixWord ++ tailWord_5775927).sum := by decide
  have hdescent : baseEnd_5775927 < baseStart_5775927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5775927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776004 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5776004 : Nat := 118140960795 + 5776004 * 2 ^ 59
def prefixEnd_5776004 : Nat := 4983230072969 + 3 ^ 40 * 5776004 * 2
def baseEnd_5776004 : Nat := 988622104764041530495549

theorem tailTrace_5776004 : CollatzResearch.WordTrace tailWord_5776004 prefixEnd_5776004 988622104764041530495549 := by
  unfold tailWord_5776004
  simp only [CollatzResearch.WordTrace]
  refine ⟨105334086483265722895991533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140445448644354297194655377 105334086483265722895991533)
  ·
    refine ⟨39500282431224646085996825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105334086483265722895991533 39500282431224646085996825)
    ·
      refine ⟨29625211823418484564497619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39500282431224646085996825 29625211823418484564497619)
      ·
        refine ⟨44437817735127726846746429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29625211823418484564497619 44437817735127726846746429)
        ·
          refine ⟨16664181650672897567529911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44437817735127726846746429 16664181650672897567529911)
          ·
            refine ⟨24996272476009346351294867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16664181650672897567529911 24996272476009346351294867)
            ·
              refine ⟨37494408714014019526942301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24996272476009346351294867 37494408714014019526942301)
              ·
                refine ⟨14060403267755257322603363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37494408714014019526942301 14060403267755257322603363)
                ·
                  refine ⟨21090604901632885983905045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14060403267755257322603363 21090604901632885983905045)
                  ·
                    refine ⟨988622104764041530495549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21090604901632885983905045 988622104764041530495549)
                    ·
                      rfl

theorem cell23_5776004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5776004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776004 prefixEnd_5776004 := by exact prefixLift 5776004
  have htrace : WordTrace (prefixWord ++ tailWord_5776004) baseStart_5776004 baseEnd_5776004 := by
    simpa [prefixWord, tailWord_5776004, baseEnd_5776004] using wordTrace_append hprefix tailTrace_5776004
  have hstable : (prefixWord ++ tailWord_5776004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776004).length < 2 ^ (prefixWord ++ tailWord_5776004).sum := by decide
  have hdescent : baseEnd_5776004 < baseStart_5776004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776024 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_5776024 : Nat := 118140960795 + 5776024 * 2 ^ 59
def prefixEnd_5776024 : Nat := 4983230072969 + 3 ^ 40 * 5776024 * 2
def baseEnd_5776024 : Nat := 2965876583905214513236555

theorem tailTrace_5776024 : CollatzResearch.WordTrace tailWord_5776024 prefixEnd_5776024 2965876583905214513236555 := by
  unfold tailWord_5776024
  simp only [CollatzResearch.WordTrace]
  refine ⟨105334451213229494603855563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140445934950972659471807417 105334451213229494603855563)
  ·
    refine ⟨158001676819844241905783345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105334451213229494603855563 158001676819844241905783345)
    ·
      refine ⟨118501257614883181429337509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158001676819844241905783345 118501257614883181429337509)
      ·
        refine ⟨22218985802790596518000783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118501257614883181429337509 22218985802790596518000783)
        ·
          refine ⟨33328478704185894777001175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22218985802790596518000783 33328478704185894777001175)
          ·
            refine ⟨49992718056278842165501763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33328478704185894777001175 49992718056278842165501763)
            ·
              refine ⟨74989077084418263248252645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49992718056278842165501763 74989077084418263248252645)
              ·
                refine ⟨14060451953328424359047371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74989077084418263248252645 14060451953328424359047371)
                ·
                  refine ⟨21090677929992636538571057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14060451953328424359047371 21090677929992636538571057)
                  ·
                    refine ⟨15818008447494477403928293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21090677929992636538571057 15818008447494477403928293)
                    ·
                      refine ⟨2965876583905214513236555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15818008447494477403928293 2965876583905214513236555)
                      ·
                        rfl

theorem cell23_5776024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_5776024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776024 prefixEnd_5776024 := by exact prefixLift 5776024
  have htrace : WordTrace (prefixWord ++ tailWord_5776024) baseStart_5776024 baseEnd_5776024 := by
    simpa [prefixWord, tailWord_5776024, baseEnd_5776024] using wordTrace_append hprefix tailTrace_5776024
  have hstable : (prefixWord ++ tailWord_5776024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776024).length < 2 ^ (prefixWord ++ tailWord_5776024).sum := by decide
  have hdescent : baseEnd_5776024 < baseStart_5776024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776028 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5776028 : Nat := 118140960795 + 5776028 * 2 ^ 59
def prefixEnd_5776028 : Nat := 4983230072969 + 3 ^ 40 * 5776028 * 2
def baseEnd_5776028 : Nat := 2965878637827832497586537

theorem tailTrace_5776028 : CollatzResearch.WordTrace tailWord_5776028 prefixEnd_5776028 2965878637827832497586537 := by
  unfold tailWord_5776028
  simp only [CollatzResearch.WordTrace]
  refine ⟨105334524159222248945428369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140446032212296331927237825 105334524159222248945428369)
  ·
    refine ⟨79000893119416686709071277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105334524159222248945428369 79000893119416686709071277)
    ·
      refine ⟨29625334919781257515901729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79000893119416686709071277 29625334919781257515901729)
      ·
        refine ⟨22219001189835943136926297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29625334919781257515901729 22219001189835943136926297)
        ·
          refine ⟨16664250892376957352694723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22219001189835943136926297 16664250892376957352694723)
          ·
            refine ⟨24996376338565436029042085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16664250892376957352694723 24996376338565436029042085)
            ·
              refine ⟨4686820563481019255445391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24996376338565436029042085 4686820563481019255445391)
              ·
                refine ⟨7030230845221528883168087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686820563481019255445391 7030230845221528883168087)
                ·
                  refine ⟨10545346267832293324752131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7030230845221528883168087 10545346267832293324752131)
                  ·
                    refine ⟨15818019401748439987128197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10545346267832293324752131 15818019401748439987128197)
                    ·
                      refine ⟨2965878637827832497586537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15818019401748439987128197 2965878637827832497586537)
                      ·
                        rfl

theorem cell23_5776028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5776028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776028 prefixEnd_5776028 := by exact prefixLift 5776028
  have htrace : WordTrace (prefixWord ++ tailWord_5776028) baseStart_5776028 baseEnd_5776028 := by
    simpa [prefixWord, tailWord_5776028, baseEnd_5776028] using wordTrace_append hprefix tailTrace_5776028
  have hstable : (prefixWord ++ tailWord_5776028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776028).length < 2 ^ (prefixWord ++ tailWord_5776028).sum := by decide
  have hdescent : baseEnd_5776028 < baseStart_5776028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776037 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_5776037 : Nat := 118140960795 + 5776037 * 2 ^ 59
def prefixEnd_5776037 : Nat := 4983230072969 + 3 ^ 40 * 5776037 * 2
def baseEnd_5776037 : Nat := 2965883259153722962373995

theorem tailTrace_5776037 : CollatzResearch.WordTrace tailWord_5776037 prefixEnd_5776037 2965883259153722962373995 := by
  unfold tailWord_5776037
  simp only [CollatzResearch.WordTrace]
  refine ⟨210669376575411892427934365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140446251050274594951956243 210669376575411892427934365)
  ·
    refine ⟨79001016215779459660475387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210669376575411892427934365 79001016215779459660475387)
    ·
      refine ⟨118501524323669189490713081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79001016215779459660475387 118501524323669189490713081)
      ·
        refine ⟨88876143242751892118034811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118501524323669189490713081 88876143242751892118034811)
        ·
          refine ⟨133314214864127838177052217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88876143242751892118034811 133314214864127838177052217)
          ·
            refine ⟨99985661148095878632789163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133314214864127838177052217 99985661148095878632789163)
            ·
              refine ⟨149978491722143817949183745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99985661148095878632789163 149978491722143817949183745)
              ·
                refine ⟨112483868791607863461887809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149978491722143817949183745 112483868791607863461887809)
                ·
                  refine ⟨84362901593705897596415857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112483868791607863461887809 84362901593705897596415857)
                  ·
                    refine ⟨63272176195279423197311893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84362901593705897596415857 63272176195279423197311893)
                    ·
                      refine ⟨2965883259153722962373995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63272176195279423197311893 2965883259153722962373995)
                      ·
                        rfl

theorem cell23_5776037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_5776037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776037 prefixEnd_5776037 := by exact prefixLift 5776037
  have htrace : WordTrace (prefixWord ++ tailWord_5776037) baseStart_5776037 baseEnd_5776037 := by
    simpa [prefixWord, tailWord_5776037, baseEnd_5776037] using wordTrace_append hprefix tailTrace_5776037
  have hstable : (prefixWord ++ tailWord_5776037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776037).length < 2 ^ (prefixWord ++ tailWord_5776037).sum := by decide
  have hdescent : baseEnd_5776037 < baseStart_5776037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776045 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_5776045 : Nat := 118140960795 + 5776045 * 2 ^ 59
def prefixEnd_5776045 : Nat := 4983230072969 + 3 ^ 40 * 5776045 * 2
def baseEnd_5776045 : Nat := 2965887366998958931073959

theorem tailTrace_5776045 : CollatzResearch.WordTrace tailWord_5776045 prefixEnd_5776045 2965887366998958931073959 := by
  unfold tailWord_5776045
  simp only [CollatzResearch.WordTrace]
  refine ⟨210669668359382909794225589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140446445572921939862817059 210669668359382909794225589)
  ·
    refine ⟨19750281408692147793208649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210669668359382909794225589 19750281408692147793208649)
    ·
      refine ⟨14812711056519110844906487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19750281408692147793208649 14812711056519110844906487)
      ·
        refine ⟨22219066584778666267359731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812711056519110844906487 22219066584778666267359731)
        ·
          refine ⟨33328599877167999401039597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22219066584778666267359731 33328599877167999401039597)
          ·
            refine ⟨12498224953937999775389849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33328599877167999401039597 12498224953937999775389849)
            ·
              refine ⟨9373668715453499831542387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12498224953937999775389849 9373668715453499831542387)
              ·
                refine ⟨14060503073180249747313581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373668715453499831542387 14060503073180249747313581)
                ·
                  refine ⟨5272688652442593655242593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14060503073180249747313581 5272688652442593655242593)
                  ·
                    refine ⟨3954516489331945241431945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272688652442593655242593 3954516489331945241431945)
                    ·
                      refine ⟨2965887366998958931073959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954516489331945241431945 2965887366998958931073959)
                      ·
                        rfl

theorem cell23_5776045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_5776045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776045 prefixEnd_5776045 := by exact prefixLift 5776045
  have htrace : WordTrace (prefixWord ++ tailWord_5776045) baseStart_5776045 baseEnd_5776045 := by
    simpa [prefixWord, tailWord_5776045, baseEnd_5776045] using wordTrace_append hprefix tailTrace_5776045
  have hstable : (prefixWord ++ tailWord_5776045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776045).length < 2 ^ (prefixWord ++ tailWord_5776045).sum := by decide
  have hdescent : baseEnd_5776045 < baseStart_5776045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776061 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_5776061 : Nat := 118140960795 + 5776061 * 2 ^ 59
def prefixEnd_5776061 : Nat := 4983230072969 + 3 ^ 40 * 5776061 * 2
def baseEnd_5776061 : Nat := 2965895582689430868473885

theorem tailTrace_5776061 : CollatzResearch.WordTrace tailWord_5776061 prefixEnd_5776061 2965895582689430868473885 := by
  unfold tailWord_5776061
  simp only [CollatzResearch.WordTrace]
  refine ⟨210670251927324944526808037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140446834618216629684538691 210670251927324944526808037)
  ·
    refine ⟨39500672236373427098776507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210670251927324944526808037 39500672236373427098776507)
    ·
      refine ⟨59251008354560140648164761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39500672236373427098776507 59251008354560140648164761)
      ·
        refine ⟨44438256265920105486123571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59251008354560140648164761 44438256265920105486123571)
        ·
          refine ⟨66657384398880158229185357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44438256265920105486123571 66657384398880158229185357)
          ·
            refine ⟨24996519149580059335944509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66657384398880158229185357 24996519149580059335944509)
            ·
              refine ⟨9373694681092522250979191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24996519149580059335944509 9373694681092522250979191)
              ·
                refine ⟨14060542021638783376468787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373694681092522250979191 14060542021638783376468787)
                ·
                  refine ⟨21090813032458175064703181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14060542021638783376468787 21090813032458175064703181)
                  ·
                    refine ⟨7909054887171815649263693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21090813032458175064703181 7909054887171815649263693)
                    ·
                      refine ⟨2965895582689430868473885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909054887171815649263693 2965895582689430868473885)
                      ·
                        rfl

theorem cell23_5776061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_5776061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776061 prefixEnd_5776061 := by exact prefixLift 5776061
  have htrace : WordTrace (prefixWord ++ tailWord_5776061) baseStart_5776061 baseEnd_5776061 := by
    simpa [prefixWord, tailWord_5776061, baseEnd_5776061] using wordTrace_append hprefix tailTrace_5776061
  have hstable : (prefixWord ++ tailWord_5776061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776061).length < 2 ^ (prefixWord ++ tailWord_5776061).sum := by decide
  have hdescent : baseEnd_5776061 < baseStart_5776061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776074 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_5776074 : Nat := 118140960795 + 5776074 * 2 ^ 59
def prefixEnd_5776074 : Nat := 4983230072969 + 3 ^ 40 * 5776074 * 2
def baseEnd_5776074 : Nat := 2965902257937939317611325

theorem tailTrace_5776074 : CollatzResearch.WordTrace tailWord_5776074 prefixEnd_5776074 2965902257937939317611325 := by
  unfold tailWord_5776074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52667681519069461936757819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140447150717518565164687517 52667681519069461936757819)
  ·
    refine ⟨79001522278604192905136729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52667681519069461936757819 79001522278604192905136729)
    ·
      refine ⟨59251141708953144678852547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79001522278604192905136729 59251141708953144678852547)
      ·
        refine ⟨88876712563429717018278821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59251141708953144678852547 88876712563429717018278821)
        ·
          refine ⟨16664383605643071940927279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88876712563429717018278821 16664383605643071940927279)
          ·
            refine ⟨24996575408464607911390919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16664383605643071940927279 24996575408464607911390919)
            ·
              refine ⟨37494863112696911867086379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24996575408464607911390919 37494863112696911867086379)
              ·
                refine ⟨56242294669045367800629569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37494863112696911867086379 56242294669045367800629569)
                ·
                  refine ⟨42181721001784025850472177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56242294669045367800629569 42181721001784025850472177)
                  ·
                    refine ⟨31636290751338019387854133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42181721001784025850472177 31636290751338019387854133)
                    ·
                      refine ⟨2965902257937939317611325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31636290751338019387854133 2965902257937939317611325)
                      ·
                        rfl

theorem cell23_5776074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_5776074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776074 prefixEnd_5776074 := by exact prefixLift 5776074
  have htrace : WordTrace (prefixWord ++ tailWord_5776074) baseStart_5776074 baseEnd_5776074 := by
    simpa [prefixWord, tailWord_5776074, baseEnd_5776074] using wordTrace_append hprefix tailTrace_5776074
  have hstable : (prefixWord ++ tailWord_5776074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776074).length < 2 ^ (prefixWord ++ tailWord_5776074).sum := by decide
  have hdescent : baseEnd_5776074 < baseStart_5776074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776088 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_5776088 : Nat := 118140960795 + 5776088 * 2 ^ 59
def prefixEnd_5776088 : Nat := 4983230072969 + 3 ^ 40 * 5776088 * 2
def baseEnd_5776088 : Nat := 2965909446667102262836261

theorem tailTrace_5776088 : CollatzResearch.WordTrace tailWord_5776088 prefixEnd_5776088 2965909446667102262836261 := by
  unfold tailWord_5776088
  simp only [CollatzResearch.WordTrace]
  refine ⟨105335618349113564069020459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140447491132151418758693945 105335618349113564069020459)
  ·
    refine ⟨158003427523670346103530689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105335618349113564069020459 158003427523670346103530689)
    ·
      refine ⟨118502570642752759577648017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158003427523670346103530689 118502570642752759577648017)
      ·
        refine ⟨88876927982064569683236013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118502570642752759577648017 88876927982064569683236013)
        ·
          refine ⟨33328847993274213631213505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88876927982064569683236013 33328847993274213631213505)
          ·
            refine ⟨24996635994955660223410129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33328847993274213631213505 24996635994955660223410129)
            ·
              refine ⟨18747476996216745167557597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24996635994955660223410129 18747476996216745167557597)
              ·
                refine ⟨7030303873581279437834099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18747476996216745167557597 7030303873581279437834099)
                ·
                  refine ⟨10545455810371919156751149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7030303873581279437834099 10545455810371919156751149)
                  ·
                    refine ⟨3954545928889469683781681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10545455810371919156751149 3954545928889469683781681)
                    ·
                      refine ⟨2965909446667102262836261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954545928889469683781681 2965909446667102262836261)
                      ·
                        rfl

theorem cell23_5776088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_5776088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776088 prefixEnd_5776088 := by exact prefixLift 5776088
  have htrace : WordTrace (prefixWord ++ tailWord_5776088) baseStart_5776088 baseEnd_5776088 := by
    simpa [prefixWord, tailWord_5776088, baseEnd_5776088] using wordTrace_append hprefix tailTrace_5776088
  have hstable : (prefixWord ++ tailWord_5776088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776088).length < 2 ^ (prefixWord ++ tailWord_5776088).sum := by decide
  have hdescent : baseEnd_5776088 < baseStart_5776088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776118 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5776118 : Nat := 118140960795 + 5776118 * 2 ^ 59
def prefixEnd_5776118 : Nat := 4983230072969 + 3 ^ 40 * 5776118 * 2
def baseEnd_5776118 : Nat := 2965924851086737145461123

theorem tailTrace_5776118 : CollatzResearch.WordTrace tailWord_5776118 prefixEnd_5776118 2965924851086737145461123 := by
  unfold tailWord_5776118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167020680507402703852063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140448220592078962174422005 13167020680507402703852063)
  ·
    refine ⟨19750531020761104055778095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167020680507402703852063 19750531020761104055778095)
    ·
      refine ⟨29625796531141656083667143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19750531020761104055778095 29625796531141656083667143)
      ·
        refine ⟨44438694796712484125500715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29625796531141656083667143 44438694796712484125500715)
        ·
          refine ⟨66658042195068726188251073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44438694796712484125500715 66658042195068726188251073)
          ·
            refine ⟨49993531646301544641188305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66658042195068726188251073 49993531646301544641188305)
            ·
              refine ⟨37495148734726158480891229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49993531646301544641188305 37495148734726158480891229)
              ·
                refine ⟨14060680775522309430334211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37495148734726158480891229 14060680775522309430334211)
                ·
                  refine ⟨21091021163283464145501317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14060680775522309430334211 21091021163283464145501317)
                  ·
                    refine ⟨3954566468115649527281497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21091021163283464145501317 3954566468115649527281497)
                    ·
                      refine ⟨2965924851086737145461123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954566468115649527281497 2965924851086737145461123)
                      ·
                        rfl

theorem cell23_5776118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5776118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776118 prefixEnd_5776118 := by exact prefixLift 5776118
  have htrace : WordTrace (prefixWord ++ tailWord_5776118) baseStart_5776118 baseEnd_5776118 := by
    simpa [prefixWord, tailWord_5776118, baseEnd_5776118] using wordTrace_append hprefix tailTrace_5776118
  have hstable : (prefixWord ++ tailWord_5776118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776118).length < 2 ^ (prefixWord ++ tailWord_5776118).sum := by decide
  have hdescent : baseEnd_5776118 < baseStart_5776118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776161 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5776161 : Nat := 118140960795 + 5776161 * 2 ^ 59
def prefixEnd_5776161 : Nat := 4983230072969 + 3 ^ 40 * 5776161 * 2
def baseEnd_5776161 : Nat := 2965946930754880477223425

theorem tailTrace_5776161 : CollatzResearch.WordTrace tailWord_5776161 prefixEnd_5776161 2965946930754880477223425 := by
  unfold tailWord_5776161
  simp only [CollatzResearch.WordTrace]
  refine ⟨210673899226962661605448337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140449266151308441070298891 210673899226962661605448337)
  ·
    refine ⟨158005424420221996204086253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210673899226962661605448337 158005424420221996204086253)
    ·
      refine ⟨59252034157583248576532345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158005424420221996204086253 59252034157583248576532345)
      ·
        refine ⟨44439025618187436432399259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59252034157583248576532345 44439025618187436432399259)
        ·
          refine ⟨66658538427281154648598889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44439025618187436432399259 66658538427281154648598889)
          ·
            refine ⟨49993903820460865986449167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66658538427281154648598889 49993903820460865986449167)
            ·
              refine ⟨74990855730691298979673751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49993903820460865986449167 74990855730691298979673751)
              ·
                refine ⟨112486283596036948469510627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74990855730691298979673751 112486283596036948469510627)
                ·
                  refine ⟨168729425394055422704265941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112486283596036948469510627 168729425394055422704265941)
                  ·
                    refine ⟨3954595907673173969631233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168729425394055422704265941 3954595907673173969631233)
                    ·
                      refine ⟨2965946930754880477223425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954595907673173969631233 2965946930754880477223425)
                      ·
                        rfl

theorem cell23_5776161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5776161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776161 prefixEnd_5776161 := by exact prefixLift 5776161
  have htrace : WordTrace (prefixWord ++ tailWord_5776161) baseStart_5776161 baseEnd_5776161 := by
    simpa [prefixWord, tailWord_5776161, baseEnd_5776161] using wordTrace_append hprefix tailTrace_5776161
  have hstable : (prefixWord ++ tailWord_5776161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776161).length < 2 ^ (prefixWord ++ tailWord_5776161).sum := by decide
  have hdescent : baseEnd_5776161 < baseStart_5776161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776191 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_5776191 : Nat := 118140960795 + 5776191 * 2 ^ 59
def prefixEnd_5776191 : Nat := 4983230072969 + 3 ^ 40 * 5776191 * 2
def baseEnd_5776191 : Nat := 2965962335174515359848287

theorem tailTrace_5776191 : CollatzResearch.WordTrace tailWord_5776191 prefixEnd_5776191 2965962335174515359848287 := by
  unfold tailWord_5776191
  simp only [CollatzResearch.WordTrace]
  refine ⟨210674993416853976729040427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140449995611235984486026951 210674993416853976729040427)
  ·
    refine ⟨316012490125280965093560641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210674993416853976729040427 316012490125280965093560641)
    ·
      refine ⟨237009367593960723820170481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316012490125280965093560641 237009367593960723820170481)
      ·
        refine ⟨177757025695470542865127861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237009367593960723820170481 177757025695470542865127861)
        ·
          refine ⟨16664721158950363393605737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177757025695470542865127861 16664721158950363393605737)
          ·
            refine ⟨12498540869212772545204303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16664721158950363393605737 12498540869212772545204303)
            ·
              refine ⟨18747811303819158817806455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12498540869212772545204303 18747811303819158817806455)
              ·
                refine ⟨28121716955728738226709683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18747811303819158817806455 28121716955728738226709683)
                ·
                  refine ⟨42182575433593107340064525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28121716955728738226709683 42182575433593107340064525)
                  ·
                    refine ⟨15818465787597415252524197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42182575433593107340064525 15818465787597415252524197)
                    ·
                      refine ⟨2965962335174515359848287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15818465787597415252524197 2965962335174515359848287)
                      ·
                        rfl

theorem cell23_5776191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_5776191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776191 prefixEnd_5776191 := by exact prefixLift 5776191
  have htrace : WordTrace (prefixWord ++ tailWord_5776191) baseStart_5776191 baseEnd_5776191 := by
    simpa [prefixWord, tailWord_5776191, baseEnd_5776191] using wordTrace_append hprefix tailTrace_5776191
  have hstable : (prefixWord ++ tailWord_5776191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776191).length < 2 ^ (prefixWord ++ tailWord_5776191).sum := by decide
  have hdescent : baseEnd_5776191 < baseStart_5776191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776211 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3]
def baseStart_5776211 : Nat := 118140960795 + 5776211 * 2 ^ 59
def prefixEnd_5776211 : Nat := 4983230072969 + 3 ^ 40 * 5776211 * 2
def baseEnd_5776211 : Nat := 2965972604787605281598195

theorem tailTrace_5776211 : CollatzResearch.WordTrace tailWord_5776211 prefixEnd_5776211 2965972604787605281598195 := by
  unfold tailWord_5776211
  simp only [CollatzResearch.WordTrace]
  refine ⟨210675722876781520144768487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140450481917854346763178991 210675722876781520144768487)
  ·
    refine ⟨316013584315172280217152731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210675722876781520144768487 316013584315172280217152731)
    ·
      refine ⟨474020376472758420325729097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316013584315172280217152731 474020376472758420325729097)
      ·
        refine ⟨355515282354568815244296823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474020376472758420325729097 355515282354568815244296823)
        ·
          refine ⟨533272923531853222866445235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355515282354568815244296823 533272923531853222866445235)
          ·
            refine ⟨799909385297779834299667853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533272923531853222866445235 799909385297779834299667853)
            ·
              refine ⟨299966019486667437862375445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799909385297779834299667853 299966019486667437862375445)
              ·
                refine ⟨14060907163437536149798849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 299966019486667437862375445 14060907163437536149798849)
                ·
                  refine ⟨10545680372578152112349137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14060907163437536149798849 10545680372578152112349137)
                  ·
                    refine ⟨7909260279433614084261853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10545680372578152112349137 7909260279433614084261853)
                    ·
                      refine ⟨2965972604787605281598195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909260279433614084261853 2965972604787605281598195)
                      ·
                        rfl

theorem cell23_5776211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_5776211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776211 prefixEnd_5776211 := by exact prefixLift 5776211
  have htrace : WordTrace (prefixWord ++ tailWord_5776211) baseStart_5776211 baseEnd_5776211 := by
    simpa [prefixWord, tailWord_5776211, baseEnd_5776211] using wordTrace_append hprefix tailTrace_5776211
  have hstable : (prefixWord ++ tailWord_5776211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776211).length < 2 ^ (prefixWord ++ tailWord_5776211).sum := by decide
  have hdescent : baseEnd_5776211 < baseStart_5776211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776218 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_5776218 : Nat := 118140960795 + 5776218 * 2 ^ 59
def prefixEnd_5776218 : Nat := 4983230072969 + 3 ^ 40 * 5776218 * 2
def baseEnd_5776218 : Nat := 988658733050728918070221

theorem tailTrace_5776218 : CollatzResearch.WordTrace tailWord_5776218 prefixEnd_5776218 988658733050728918070221 := by
  unfold tailWord_5776218
  simp only [CollatzResearch.WordTrace]
  refine ⟨52668994546939040085068327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140450652125170773560182205 52668994546939040085068327)
  ·
    refine ⟨79003491820408560127602491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52668994546939040085068327 79003491820408560127602491)
    ·
      refine ⟨118505237730612840191403737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79003491820408560127602491 118505237730612840191403737)
      ·
        refine ⟨88878928297959630143552803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118505237730612840191403737 88878928297959630143552803)
        ·
          refine ⟨133318392446939445215329205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88878928297959630143552803 133318392446939445215329205)
          ·
            refine ⟨12498599291900572988937113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133318392446939445215329205 12498599291900572988937113)
            ·
              refine ⟨9373949468925429741702835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12498599291900572988937113 9373949468925429741702835)
              ·
                refine ⟨14060924203388144612554253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373949468925429741702835 14060924203388144612554253)
                ·
                  refine ⟨5272846576270554229707845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14060924203388144612554253 5272846576270554229707845)
                  ·
                    refine ⟨988658733050728918070221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272846576270554229707845 988658733050728918070221)
                    ·
                      rfl

theorem cell23_5776218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_5776218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776218 prefixEnd_5776218 := by exact prefixLift 5776218
  have htrace : WordTrace (prefixWord ++ tailWord_5776218) baseStart_5776218 baseEnd_5776218 := by
    simpa [prefixWord, tailWord_5776218, baseEnd_5776218] using wordTrace_append hprefix tailTrace_5776218
  have hstable : (prefixWord ++ tailWord_5776218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776218).length < 2 ^ (prefixWord ++ tailWord_5776218).sum := by decide
  have hdescent : baseEnd_5776218 < baseStart_5776218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776268 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_5776268 : Nat := 118140960795 + 5776268 * 2 ^ 59
def prefixEnd_5776268 : Nat := 4983230072969 + 3 ^ 40 * 5776268 * 2
def baseEnd_5776268 : Nat := 2966001873184911558585433

theorem tailTrace_5776268 : CollatzResearch.WordTrace tailWord_5776268 prefixEnd_5776268 2966001873184911558585433 := by
  unfold tailWord_5776268
  simp only [CollatzResearch.WordTrace]
  refine ⟨105338900918787509439796729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140451867891716679253062305 105338900918787509439796729)
  ·
    refine ⟨79004175689090632079847547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105338900918787509439796729 79004175689090632079847547)
    ·
      refine ⟨118506263533635948119771321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79004175689090632079847547 118506263533635948119771321)
      ·
        refine ⟨88879697650226961089828491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118506263533635948119771321 88879697650226961089828491)
        ·
          refine ⟨133319546475340441634742737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88879697650226961089828491 133319546475340441634742737)
          ·
            refine ⟨99989659856505331226057053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133319546475340441634742737 99989659856505331226057053)
            ·
              refine ⟨37496122446189499209771395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99989659856505331226057053 37496122446189499209771395)
              ·
                refine ⟨56244183669284248814657093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37496122446189499209771395 56244183669284248814657093)
                ·
                  refine ⟨10545784437990796652748205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56244183669284248814657093 10545784437990796652748205)
                  ·
                    refine ⟨3954669164246548744780577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10545784437990796652748205 3954669164246548744780577)
                    ·
                      refine ⟨2966001873184911558585433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954669164246548744780577 2966001873184911558585433)
                      ·
                        rfl

theorem cell23_5776268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_5776268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776268 prefixEnd_5776268 := by exact prefixLift 5776268
  have htrace : WordTrace (prefixWord ++ tailWord_5776268) baseStart_5776268 baseEnd_5776268 := by
    simpa [prefixWord, tailWord_5776268, baseEnd_5776268] using wordTrace_append hprefix tailTrace_5776268
  have hstable : (prefixWord ++ tailWord_5776268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776268).length < 2 ^ (prefixWord ++ tailWord_5776268).sum := by decide
  have hdescent : baseEnd_5776268 < baseStart_5776268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776281 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_5776281 : Nat := 118140960795 + 5776281 * 2 ^ 59
def prefixEnd_5776281 : Nat := 4983230072969 + 3 ^ 40 * 5776281 * 2
def baseEnd_5776281 : Nat := 2966008548433420007722873

theorem tailTrace_5776281 : CollatzResearch.WordTrace tailWord_5776281 prefixEnd_5776281 2966008548433420007722873 := by
  unfold tailWord_5776281
  simp only [CollatzResearch.WordTrace]
  refine ⟨210678275986527922099816697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140452183991018614733211131 210678275986527922099816697)
  ·
    refine ⟨158008706989895941574862523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210678275986527922099816697 158008706989895941574862523)
    ·
      refine ⟨237013060484843912362293785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158008706989895941574862523 237013060484843912362293785)
      ·
        refine ⟨177759795363632934271720339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237013060484843912362293785 177759795363632934271720339)
        ·
          refine ⟨266639693045449401407580509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177759795363632934271720339 266639693045449401407580509)
          ·
            refine ⟨99989884892043525527842691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266639693045449401407580509 99989884892043525527842691)
            ·
              refine ⟨149984827338065288291764037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99989884892043525527842691 149984827338065288291764037)
              ·
                refine ⟨28122155125887241554705757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149984827338065288291764037 28122155125887241554705757)
                ·
                  refine ⟨10545808172207715583014659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28122155125887241554705757 10545808172207715583014659)
                  ·
                    refine ⟨15818712258311573374521989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10545808172207715583014659 15818712258311573374521989)
                    ·
                      refine ⟨2966008548433420007722873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15818712258311573374521989 2966008548433420007722873)
                      ·
                        rfl

theorem cell23_5776281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_5776281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776281 prefixEnd_5776281 := by exact prefixLift 5776281
  have htrace : WordTrace (prefixWord ++ tailWord_5776281) baseStart_5776281 baseEnd_5776281 := by
    simpa [prefixWord, tailWord_5776281, baseEnd_5776281] using wordTrace_append hprefix tailTrace_5776281
  have hstable : (prefixWord ++ tailWord_5776281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776281).length < 2 ^ (prefixWord ++ tailWord_5776281).sum := by decide
  have hdescent : baseEnd_5776281 < baseStart_5776281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776282 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_5776282 : Nat := 118140960795 + 5776282 * 2 ^ 59
def prefixEnd_5776282 : Nat := 4983230072969 + 3 ^ 40 * 5776282 * 2
def baseEnd_5776282 : Nat := 329556562434897167090041

theorem tailTrace_5776282 : CollatzResearch.WordTrace tailWord_5776282 prefixEnd_5776282 329556562434897167090041 := by
  unfold tailWord_5776282
  simp only [CollatzResearch.WordTrace]
  refine ⟨52669578114881074817650775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140452208306349532847068733 52669578114881074817650775)
  ·
    refine ⟨79004367172321612226476163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52669578114881074817650775 79004367172321612226476163)
    ·
      refine ⟨118506550758482418339714245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79004367172321612226476163 118506550758482418339714245)
      ·
        refine ⟨22219978267215453438696421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118506550758482418339714245 22219978267215453438696421)
        ·
          refine ⟨4166245925102897519755579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22219978267215453438696421 4166245925102897519755579)
          ·
            refine ⟨6249368887654346279633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166245925102897519755579 6249368887654346279633369)
            ·
              refine ⟨4687026665740759709725027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249368887654346279633369 4687026665740759709725027)
              ·
                refine ⟨7030539998611139564587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687026665740759709725027 7030539998611139564587541)
                ·
                  refine ⟨329556562434897167090041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7030539998611139564587541 329556562434897167090041)
                  ·
                    rfl

theorem cell23_5776282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_5776282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776282 prefixEnd_5776282 := by exact prefixLift 5776282
  have htrace : WordTrace (prefixWord ++ tailWord_5776282) baseStart_5776282 baseEnd_5776282 := by
    simpa [prefixWord, tailWord_5776282, baseEnd_5776282] using wordTrace_append hprefix tailTrace_5776282
  have hstable : (prefixWord ++ tailWord_5776282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776282).length < 2 ^ (prefixWord ++ tailWord_5776282).sum := by decide
  have hdescent : baseEnd_5776282 < baseStart_5776282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776311 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_5776311 : Nat := 118140960795 + 5776311 * 2 ^ 59
def prefixEnd_5776311 : Nat := 4983230072969 + 3 ^ 40 * 5776311 * 2
def baseEnd_5776311 : Nat := 2966023952853054890347735

theorem tailTrace_5776311 : CollatzResearch.WordTrace tailWord_5776311 prefixEnd_5776311 2966023952853054890347735 := by
  unfold tailWord_5776311
  simp only [CollatzResearch.WordTrace]
  refine ⟨210679370176419237223408787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140452913450946158148939191 210679370176419237223408787)
  ·
    refine ⟨316019055264628855835113181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210679370176419237223408787 316019055264628855835113181)
    ·
      refine ⟨118507145724235820938167443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316019055264628855835113181 118507145724235820938167443)
      ·
        refine ⟨177760718586353731407251165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118507145724235820938167443 177760718586353731407251165)
        ·
          refine ⟨66660269469882649277719187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177760718586353731407251165 66660269469882649277719187)
          ·
            refine ⟨99990404204823973916578781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66660269469882649277719187 99990404204823973916578781)
            ·
              refine ⟨37496401576808990218717043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99990404204823973916578781 37496401576808990218717043)
              ·
                refine ⟨56244602365213485328075565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37496401576808990218717043 56244602365213485328075565)
                ·
                  refine ⟨21091725886955056998028337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56244602365213485328075565 21091725886955056998028337)
                  ·
                    refine ⟨15818794415216292748521253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21091725886955056998028337 15818794415216292748521253)
                    ·
                      refine ⟨2966023952853054890347735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15818794415216292748521253 2966023952853054890347735)
                      ·
                        rfl

theorem cell23_5776311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_5776311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776311 prefixEnd_5776311 := by exact prefixLift 5776311
  have htrace : WordTrace (prefixWord ++ tailWord_5776311) baseStart_5776311 baseEnd_5776311 := by
    simpa [prefixWord, tailWord_5776311, baseEnd_5776311] using wordTrace_append hprefix tailTrace_5776311
  have hstable : (prefixWord ++ tailWord_5776311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776311).length < 2 ^ (prefixWord ++ tailWord_5776311).sum := by decide
  have hdescent : baseEnd_5776311 < baseStart_5776311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776338 : List Nat := [3, 2, 2, 3, 1, 1, 3, 8]
def baseStart_5776338 : Nat := 118140960795 + 5776338 * 2 ^ 59
def prefixEnd_5776338 : Nat := 4983230072969 + 3 ^ 40 * 5776338 * 2
def baseEnd_5776338 : Nat := 109853252475212084618893

theorem tailTrace_5776338 : CollatzResearch.WordTrace tailWord_5776338 prefixEnd_5776338 109853252475212084618893 := by
  unfold tailWord_5776338
  simp only [CollatzResearch.WordTrace]
  refine ⟨52670088736830355208660417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140453569964880947223094445 52670088736830355208660417)
  ·
    refine ⟨39502566552622766406495313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52670088736830355208660417 39502566552622766406495313)
    ·
      refine ⟨29626924914467074804871485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39502566552622766406495313 29626924914467074804871485)
      ·
        refine ⟨11110096842925153051826807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29626924914467074804871485 11110096842925153051826807)
        ·
          refine ⟨16665145264387729577740211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11110096842925153051826807 16665145264387729577740211)
          ·
            refine ⟨24997717896581594366610317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665145264387729577740211 24997717896581594366610317)
            ·
              refine ⟨9374144211218097887478869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24997717896581594366610317 9374144211218097887478869)
              ·
                refine ⟨109853252475212084618893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9374144211218097887478869 109853252475212084618893)
                ·
                  rfl

theorem cell23_5776338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_5776338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776338 prefixEnd_5776338 := by exact prefixLift 5776338
  have htrace : WordTrace (prefixWord ++ tailWord_5776338) baseStart_5776338 baseEnd_5776338 := by
    simpa [prefixWord, tailWord_5776338, baseEnd_5776338] using wordTrace_append hprefix tailTrace_5776338
  have hstable : (prefixWord ++ tailWord_5776338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776338).length < 2 ^ (prefixWord ++ tailWord_5776338).sum := by decide
  have hdescent : baseEnd_5776338 < baseStart_5776338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776342 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5776342 : Nat := 118140960795 + 5776342 * 2 ^ 59
def prefixEnd_5776342 : Nat := 4983230072969 + 3 ^ 40 * 5776342 * 2
def baseEnd_5776342 : Nat := 988679956917781423020031

theorem tailTrace_5776342 : CollatzResearch.WordTrace tailWord_5776342 prefixEnd_5776342 988679956917781423020031 := by
  unfold tailWord_5776342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167531302456683094861705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140453667226204619678524853 13167531302456683094861705)
  ·
    refine ⟨9875648476842512321146279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13167531302456683094861705 9875648476842512321146279)
    ·
      refine ⟨14813472715263768481719419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9875648476842512321146279 14813472715263768481719419)
      ·
        refine ⟨22220209072895652722579129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14813472715263768481719419 22220209072895652722579129)
        ·
          refine ⟨16665156804671739541934347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22220209072895652722579129 16665156804671739541934347)
          ·
            refine ⟨24997735207007609312901521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665156804671739541934347 24997735207007609312901521)
            ·
              refine ⟨18748301405255706984676141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24997735207007609312901521 18748301405255706984676141)
              ·
                refine ⟨7030613026970890119253553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18748301405255706984676141 7030613026970890119253553)
                ·
                  refine ⟨5272959770228167589440165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7030613026970890119253553 5272959770228167589440165)
                  ·
                    refine ⟨988679956917781423020031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272959770228167589440165 988679956917781423020031)
                    ·
                      rfl

theorem cell23_5776342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5776342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776342 prefixEnd_5776342 := by exact prefixLift 5776342
  have htrace : WordTrace (prefixWord ++ tailWord_5776342) baseStart_5776342 baseEnd_5776342 := by
    simpa [prefixWord, tailWord_5776342, baseEnd_5776342] using wordTrace_append hprefix tailTrace_5776342
  have hstable : (prefixWord ++ tailWord_5776342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776342).length < 2 ^ (prefixWord ++ tailWord_5776342).sum := by decide
  have hdescent : baseEnd_5776342 < baseStart_5776342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776366 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_5776366 : Nat := 118140960795 + 5776366 * 2 ^ 59
def prefixEnd_5776366 : Nat := 4983230072969 + 3 ^ 40 * 5776366 * 2
def baseEnd_5776366 : Nat := 2966052194289052175159983

theorem tailTrace_5776366 : CollatzResearch.WordTrace tailWord_5776366 prefixEnd_5776366 2966052194289052175159983 := by
  unfold tailWord_5776366
  simp only [CollatzResearch.WordTrace]
  refine ⟨26335172023902497702082619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140454250794146654411107301 26335172023902497702082619)
  ·
    refine ⟨39502758035853746553123929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26335172023902497702082619 39502758035853746553123929)
    ·
      refine ⟨29627068526890309914842947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39502758035853746553123929 29627068526890309914842947)
      ·
        refine ⟨44440602790335464872264421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29627068526890309914842947 44440602790335464872264421)
        ·
          refine ⟨8332613023187899663549579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44440602790335464872264421 8332613023187899663549579)
          ·
            refine ⟨12498919534781849495324369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332613023187899663549579 12498919534781849495324369)
            ·
              refine ⟨9374189651086387121493277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12498919534781849495324369 9374189651086387121493277)
              ·
                refine ⟨3515321119157395170559979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9374189651086387121493277 3515321119157395170559979)
                ·
                  refine ⟨5272981678736092755839969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515321119157395170559979 5272981678736092755839969)
                  ·
                    refine ⟨3954736259052069566879977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5272981678736092755839969 3954736259052069566879977)
                    ·
                      refine ⟨2966052194289052175159983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954736259052069566879977 2966052194289052175159983)
                      ·
                        rfl

theorem cell23_5776366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_5776366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776366 prefixEnd_5776366 := by exact prefixLift 5776366
  have htrace : WordTrace (prefixWord ++ tailWord_5776366) baseStart_5776366 baseEnd_5776366 := by
    simpa [prefixWord, tailWord_5776366, baseEnd_5776366] using wordTrace_append hprefix tailTrace_5776366
  have hstable : (prefixWord ++ tailWord_5776366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776366).length < 2 ^ (prefixWord ++ tailWord_5776366).sum := by decide
  have hdescent : baseEnd_5776366 < baseStart_5776366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776398 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_5776398 : Nat := 118140960795 + 5776398 * 2 ^ 59
def prefixEnd_5776398 : Nat := 4983230072969 + 3 ^ 40 * 5776398 * 2
def baseEnd_5776398 : Nat := 988689541889998683319945

theorem tailTrace_5776398 : CollatzResearch.WordTrace tailWord_5776398 prefixEnd_5776398 988689541889998683319945 := by
  unfold tailWord_5776398
  simp only [CollatzResearch.WordTrace]
  refine ⟨26335317915888006385228231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140455028884736034054550565 26335317915888006385228231)
  ·
    refine ⟨39502976873832009577842347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26335317915888006385228231 39502976873832009577842347)
    ·
      refine ⟨59254465310748014366763521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39502976873832009577842347 59254465310748014366763521)
      ·
        refine ⟨44440848983061010775072641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59254465310748014366763521 44440848983061010775072641)
        ·
          refine ⟨33330636737295758081304481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44440848983061010775072641 33330636737295758081304481)
          ·
            refine ⟨24997977552971818560978361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33330636737295758081304481 24997977552971818560978361)
            ·
              refine ⟨18748483164728863920733771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24997977552971818560978361 18748483164728863920733771)
              ·
                refine ⟨28122724747093295881100657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18748483164728863920733771 28122724747093295881100657)
                ·
                  refine ⟨21092043560319971910825493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28122724747093295881100657 21092043560319971910825493)
                  ·
                    refine ⟨988689541889998683319945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21092043560319971910825493 988689541889998683319945)
                    ·
                      rfl

theorem cell23_5776398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_5776398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776398 prefixEnd_5776398 := by exact prefixLift 5776398
  have htrace : WordTrace (prefixWord ++ tailWord_5776398) baseStart_5776398 baseEnd_5776398 := by
    simpa [prefixWord, tailWord_5776398, baseEnd_5776398] using wordTrace_append hprefix tailTrace_5776398
  have hstable : (prefixWord ++ tailWord_5776398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776398).length < 2 ^ (prefixWord ++ tailWord_5776398).sum := by decide
  have hdescent : baseEnd_5776398 < baseStart_5776398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776445 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 7]
def baseStart_5776445 : Nat := 118140960795 + 5776445 * 2 ^ 59
def prefixEnd_5776445 : Nat := 4983230072969 + 3 ^ 40 * 5776445 * 2
def baseEnd_5776445 : Nat := 329565862140084151785791

theorem tailTrace_5776445 : CollatzResearch.WordTrace tailWord_5776445 prefixEnd_5776445 329565862140084151785791 := by
  unfold tailWord_5776445
  simp only [CollatzResearch.WordTrace]
  refine ⟨210684257557933778108786789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140456171705289185405857859 210684257557933778108786789)
  ·
    refine ⟨39503298292112583395397523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210684257557933778108786789 39503298292112583395397523)
    ·
      refine ⟨59254947438168875093096285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39503298292112583395397523 59254947438168875093096285)
      ·
        refine ⟨22220605289313328159911107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59254947438168875093096285 22220605289313328159911107)
        ·
          refine ⟨33330907933969992239866661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22220605289313328159911107 33330907933969992239866661)
          ·
            refine ⟨6249545237619373544974999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33330907933969992239866661 6249545237619373544974999)
            ·
              refine ⟨9374317856429060317462499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249545237619373544974999 9374317856429060317462499)
              ·
                refine ⟨14061476784643590476193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374317856429060317462499 14061476784643590476193749)
                ·
                  refine ⟨329565862140084151785791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14061476784643590476193749 329565862140084151785791)
                  ·
                    rfl

theorem cell23_5776445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_5776445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776445 prefixEnd_5776445 := by exact prefixLift 5776445
  have htrace : WordTrace (prefixWord ++ tailWord_5776445) baseStart_5776445 baseEnd_5776445 := by
    simpa [prefixWord, tailWord_5776445, baseEnd_5776445] using wordTrace_append hprefix tailTrace_5776445
  have hstable : (prefixWord ++ tailWord_5776445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776445).length < 2 ^ (prefixWord ++ tailWord_5776445).sum := by decide
  have hdescent : baseEnd_5776445 < baseStart_5776445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776495 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 4, 2]
def baseStart_5776495 : Nat := 118140960795 + 5776495 * 2 ^ 59
def prefixEnd_5776495 : Nat := 4983230072969 + 3 ^ 40 * 5776495 * 2
def baseEnd_5776495 : Nat := 2966118433293482170446889

theorem tailTrace_5776495 : CollatzResearch.WordTrace tailWord_5776495 prefixEnd_5776495 2966118433293482170446889 := by
  unfold tailWord_5776495
  simp only [CollatzResearch.WordTrace]
  refine ⟨210686081207752636648106939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140457387471835091098737959 210686081207752636648106939)
  ·
    refine ⟨316029121811628954972160409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210686081207752636648106939 316029121811628954972160409)
    ·
      refine ⟨237021841358721716229120307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316029121811628954972160409 237021841358721716229120307)
      ·
        refine ⟨355532762038082574343680461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237021841358721716229120307 355532762038082574343680461)
        ·
          refine ⟨133324785764280965378880173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355532762038082574343680461 133324785764280965378880173)
          ·
            refine ⟨49996794661605362017080065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133324785764280965378880173 49996794661605362017080065)
            ·
              refine ⟨37497595996204021512810049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49996794661605362017080065 37497595996204021512810049)
              ·
                refine ⟨28123196997153016134607537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37497595996204021512810049 28123196997153016134607537)
                ·
                  refine ⟨21092397747864762100955653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28123196997153016134607537 21092397747864762100955653)
                  ·
                    refine ⟨3954824577724642893929185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21092397747864762100955653 3954824577724642893929185)
                    ·
                      refine ⟨2966118433293482170446889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954824577724642893929185 2966118433293482170446889)
                      ·
                        rfl

theorem cell23_5776495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 4, 2].length) (baseStart_5776495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776495 prefixEnd_5776495 := by exact prefixLift 5776495
  have htrace : WordTrace (prefixWord ++ tailWord_5776495) baseStart_5776495 baseEnd_5776495 := by
    simpa [prefixWord, tailWord_5776495, baseEnd_5776495] using wordTrace_append hprefix tailTrace_5776495
  have hstable : (prefixWord ++ tailWord_5776495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776495).length < 2 ^ (prefixWord ++ tailWord_5776495).sum := by decide
  have hdescent : baseEnd_5776495 < baseStart_5776495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776498 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_5776498 : Nat := 118140960795 + 5776498 * 2 ^ 59
def prefixEnd_5776498 : Nat := 4983230072969 + 3 ^ 40 * 5776498 * 2
def baseEnd_5776498 : Nat := 2966119973735445658709375

theorem tailTrace_5776498 : CollatzResearch.WordTrace tailWord_5776498 prefixEnd_5776498 2966119973735445658709375 := by
  unfold tailWord_5776498
  simp only [CollatzResearch.WordTrace]
  refine ⟨52671547656685442040116537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140457460417827845440310765 52671547656685442040116537)
  ·
    refine ⟨39503660742514081530087403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52671547656685442040116537 39503660742514081530087403)
    ·
      refine ⟨59255491113771122295131105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39503660742514081530087403 59255491113771122295131105)
      ·
        refine ⟨44441618335328341721348329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59255491113771122295131105 44441618335328341721348329)
        ·
          refine ⟨33331213751496256291011247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44441618335328341721348329 33331213751496256291011247)
          ·
            refine ⟨49996820627244384436516871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33331213751496256291011247 49996820627244384436516871)
            ·
              refine ⟨74995230940866576654775307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49996820627244384436516871 74995230940866576654775307)
              ·
                refine ⟨112492846411299864982162961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74995230940866576654775307 112492846411299864982162961)
                ·
                  refine ⟨84369634808474898736622221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112492846411299864982162961 84369634808474898736622221)
                  ·
                    refine ⟨31638613053178087026233333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84369634808474898736622221 31638613053178087026233333)
                    ·
                      refine ⟨2966119973735445658709375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31638613053178087026233333 2966119973735445658709375)
                      ·
                        rfl

theorem cell23_5776498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_5776498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776498 prefixEnd_5776498 := by exact prefixLift 5776498
  have htrace : WordTrace (prefixWord ++ tailWord_5776498) baseStart_5776498 baseEnd_5776498 := by
    simpa [prefixWord, tailWord_5776498, baseEnd_5776498] using wordTrace_append hprefix tailTrace_5776498
  have hstable : (prefixWord ++ tailWord_5776498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776498).length < 2 ^ (prefixWord ++ tailWord_5776498).sum := by decide
  have hdescent : baseEnd_5776498 < baseStart_5776498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776528 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_5776528 : Nat := 118140960795 + 5776528 * 2 ^ 59
def prefixEnd_5776528 : Nat := 4983230072969 + 3 ^ 40 * 5776528 * 2
def baseEnd_5776528 : Nat := 2966135378155080541334237

theorem tailTrace_5776528 : CollatzResearch.WordTrace tailWord_5776528 prefixEnd_5776528 2966135378155080541334237 := by
  unfold tailWord_5776528
  simp only [CollatzResearch.WordTrace]
  refine ⟨105343642408316541642029119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140458189877755388856038825 105343642408316541642029119)
  ·
    refine ⟨158015463612474812463043679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105343642408316541642029119 158015463612474812463043679)
    ·
      refine ⟨237023195418712218694565519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158015463612474812463043679 237023195418712218694565519)
      ·
        refine ⟨355534793128068328041848279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237023195418712218694565519 355534793128068328041848279)
        ·
          refine ⟨533302189692102492062772419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355534793128068328041848279 533302189692102492062772419)
          ·
            refine ⟨799953284538153738094158629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533302189692102492062772419 799953284538153738094158629)
            ·
              refine ⟨149991240850903825892654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 799953284538153738094158629 149991240850903825892654743)
              ·
                refine ⟨224986861276355738838982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149991240850903825892654743 224986861276355738838982115)
                ·
                  refine ⟨337480291914533608258473173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224986861276355738838982115 337480291914533608258473173)
                  ·
                    refine ⟨7909694341746881443557965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 337480291914533608258473173 7909694341746881443557965)
                    ·
                      refine ⟨2966135378155080541334237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909694341746881443557965 2966135378155080541334237)
                      ·
                        rfl

theorem cell23_5776528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_5776528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776528 prefixEnd_5776528 := by exact prefixLift 5776528
  have htrace : WordTrace (prefixWord ++ tailWord_5776528) baseStart_5776528 baseEnd_5776528 := by
    simpa [prefixWord, tailWord_5776528, baseEnd_5776528] using wordTrace_append hprefix tailTrace_5776528
  have hstable : (prefixWord ++ tailWord_5776528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776528).length < 2 ^ (prefixWord ++ tailWord_5776528).sum := by decide
  have hdescent : baseEnd_5776528 < baseStart_5776528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776562 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_5776562 : Nat := 118140960795 + 5776562 * 2 ^ 59
def prefixEnd_5776562 : Nat := 4983230072969 + 3 ^ 40 * 5776562 * 2
def baseEnd_5776562 : Nat := 2966152836497333408309081

theorem tailTrace_5776562 : CollatzResearch.WordTrace tailWord_5776562 prefixEnd_5776562 2966152836497333408309081 := by
  unfold tailWord_5776562
  simp only [CollatzResearch.WordTrace]
  refine ⟨52672131224627476772698985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140459016599006604727197293 52672131224627476772698985)
  ·
    refine ⟨39504098418470607579524239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52672131224627476772698985 39504098418470607579524239)
    ·
      refine ⟨59256147627705911369286359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39504098418470607579524239 59256147627705911369286359)
      ·
        refine ⟨88884221441558867053929539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59256147627705911369286359 88884221441558867053929539)
        ·
          refine ⟨133326332162338300580894309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88884221441558867053929539 133326332162338300580894309)
          ·
            refine ⟨24998687280438431358917683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133326332162338300580894309 24998687280438431358917683)
            ·
              refine ⟨37498030920657647038376525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24998687280438431358917683 37498030920657647038376525)
              ·
                refine ⟨14061761595246617639391197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37498030920657647038376525 14061761595246617639391197)
                ·
                  refine ⟨5273160598217481614771699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14061761595246617639391197 5273160598217481614771699)
                  ·
                    refine ⟨7909740897326222422157549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273160598217481614771699 7909740897326222422157549)
                    ·
                      refine ⟨2966152836497333408309081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909740897326222422157549 2966152836497333408309081)
                      ·
                        rfl

theorem cell23_5776562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_5776562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776562 prefixEnd_5776562 := by exact prefixLift 5776562
  have htrace : WordTrace (prefixWord ++ tailWord_5776562) baseStart_5776562 baseEnd_5776562 := by
    simpa [prefixWord, tailWord_5776562, baseEnd_5776562] using wordTrace_append hprefix tailTrace_5776562
  have hstable : (prefixWord ++ tailWord_5776562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776562).length < 2 ^ (prefixWord ++ tailWord_5776562).sum := by decide
  have hdescent : baseEnd_5776562 < baseStart_5776562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776568 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_5776568 : Nat := 118140960795 + 5776568 * 2 ^ 59
def prefixEnd_5776568 : Nat := 4983230072969 + 3 ^ 40 * 5776568 * 2
def baseEnd_5776568 : Nat := 2966155917381260384834053

theorem tailTrace_5776568 : CollatzResearch.WordTrace tailWord_5776568 prefixEnd_5776568 2966155917381260384834053 := by
  unfold tailWord_5776568
  simp only [CollatzResearch.WordTrace]
  refine ⟨105344371868244085057757179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140459162490992113410342905 105344371868244085057757179)
  ·
    refine ⟨158016557802366127586635769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105344371868244085057757179 158016557802366127586635769)
    ·
      refine ⟨118512418351774595689976827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158016557802366127586635769 118512418351774595689976827)
      ·
        refine ⟨177768627527661893534965241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118512418351774595689976827 177768627527661893534965241)
        ·
          refine ⟨133326470645746420151223931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177768627527661893534965241 133326470645746420151223931)
          ·
            refine ⟨199989705968619630226835897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133326470645746420151223931 199989705968619630226835897)
            ·
              refine ⟨149992279476464722670126923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199989705968619630226835897 149992279476464722670126923)
              ·
                refine ⟨224988419214697084005190385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149992279476464722670126923 224988419214697084005190385)
                ·
                  refine ⟨168741314411022813003892789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224988419214697084005190385 168741314411022813003892789)
                  ·
                    refine ⟨15819498226033388719114949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168741314411022813003892789 15819498226033388719114949)
                    ·
                      refine ⟨2966155917381260384834053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15819498226033388719114949 2966155917381260384834053)
                      ·
                        rfl

theorem cell23_5776568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_5776568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776568 prefixEnd_5776568 := by exact prefixLift 5776568
  have htrace : WordTrace (prefixWord ++ tailWord_5776568) baseStart_5776568 baseEnd_5776568 := by
    simpa [prefixWord, tailWord_5776568, baseEnd_5776568] using wordTrace_append hprefix tailTrace_5776568
  have hstable : (prefixWord ++ tailWord_5776568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776568).length < 2 ^ (prefixWord ++ tailWord_5776568).sum := by decide
  have hdescent : baseEnd_5776568 < baseStart_5776568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776572 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5776572 : Nat := 118140960795 + 5776572 * 2 ^ 59
def prefixEnd_5776572 : Nat := 4983230072969 + 3 ^ 40 * 5776572 * 2
def baseEnd_5776572 : Nat := 2966157971303878369184035

theorem tailTrace_5776572 : CollatzResearch.WordTrace tailWord_5776572 prefixEnd_5776572 2966157971303878369184035 := by
  unfold tailWord_5776572
  simp only [CollatzResearch.WordTrace]
  refine ⟨105344444814236839399329985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140459259752315785865773313 105344444814236839399329985)
  ·
    refine ⟨79008333610677629549497489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105344444814236839399329985 79008333610677629549497489)
    ·
      refine ⟨59256250208008222162123117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79008333610677629549497489 59256250208008222162123117)
      ·
        refine ⟨22221093828003083310796169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59256250208008222162123117 22221093828003083310796169)
        ·
          refine ⟨16665820371002312483097127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22221093828003083310796169 16665820371002312483097127)
          ·
            refine ⟨24998730556503468724645691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665820371002312483097127 24998730556503468724645691)
            ·
              refine ⟨37498095834755203086968537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24998730556503468724645691 37498095834755203086968537)
              ·
                refine ⟨28123571876066402315226403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37498095834755203086968537 28123571876066402315226403)
                ·
                  refine ⟨42185357814099603472839605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28123571876066402315226403 42185357814099603472839605)
                  ·
                    refine ⟨3954877295071837825578713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42185357814099603472839605 3954877295071837825578713)
                    ·
                      refine ⟨2966157971303878369184035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954877295071837825578713 2966157971303878369184035)
                      ·
                        rfl

theorem cell23_5776572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5776572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776572 prefixEnd_5776572 := by exact prefixLift 5776572
  have htrace : WordTrace (prefixWord ++ tailWord_5776572) baseStart_5776572 baseEnd_5776572 := by
    simpa [prefixWord, tailWord_5776572, baseEnd_5776572] using wordTrace_append hprefix tailTrace_5776572
  have hstable : (prefixWord ++ tailWord_5776572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776572).length < 2 ^ (prefixWord ++ tailWord_5776572).sum := by decide
  have hdescent : baseEnd_5776572 < baseStart_5776572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776608 : List Nat := [2, 1, 1, 3, 1, 4, 11]
def baseStart_5776608 : Nat := 118140960795 + 5776608 * 2 ^ 59
def prefixEnd_5776608 : Nat := 4983230072969 + 3 ^ 40 * 5776608 * 2
def baseEnd_5776608 : Nat := 36619462427252348497949

theorem tailTrace_5776608 : CollatzResearch.WordTrace tailWord_5776608 prefixEnd_5776608 36619462427252348497949 := by
  unfold tailWord_5776608
  simp only [CollatzResearch.WordTrace]
  refine ⟨105345101328171628473485239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140460135104228837964646985 105345101328171628473485239)
  ·
    refine ⟨158017651992257442710227859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105345101328171628473485239 158017651992257442710227859)
    ·
      refine ⟨237026477988386164065341789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158017651992257442710227859 237026477988386164065341789)
      ·
        refine ⟨88884929245644811524503171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237026477988386164065341789 88884929245644811524503171)
        ·
          refine ⟨133327393868467217286754757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88884929245644811524503171 133327393868467217286754757)
          ·
            refine ⟨24998886350337603241266517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133327393868467217286754757 24998886350337603241266517)
            ·
              refine ⟨36619462427252348497949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24998886350337603241266517 36619462427252348497949)
              ·
                rfl

theorem cell23_5776608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 11].length) (baseStart_5776608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776608 prefixEnd_5776608 := by exact prefixLift 5776608
  have htrace : WordTrace (prefixWord ++ tailWord_5776608) baseStart_5776608 baseEnd_5776608 := by
    simpa [prefixWord, tailWord_5776608, baseEnd_5776608] using wordTrace_append hprefix tailTrace_5776608
  have hstable : (prefixWord ++ tailWord_5776608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776608).length < 2 ^ (prefixWord ++ tailWord_5776608).sum := by decide
  have hdescent : baseEnd_5776608 < baseStart_5776608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776613 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5776613 : Nat := 118140960795 + 5776613 * 2 ^ 59
def prefixEnd_5776613 : Nat := 4983230072969 + 3 ^ 40 * 5776613 * 2
def baseEnd_5776613 : Nat := 2966179024010712708771347

theorem tailTrace_5776613 : CollatzResearch.WordTrace tailWord_5776613 prefixEnd_5776613 2966179024010712708771347 := by
  unfold tailWord_5776613
  simp only [CollatzResearch.WordTrace]
  refine ⟨210690385021325142800902493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140460256680883428533934995 210690385021325142800902493)
  ·
    refine ⟨79008894382996928550338435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210690385021325142800902493 79008894382996928550338435)
    ·
      refine ⟨118513341574495392825507653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79008894382996928550338435 118513341574495392825507653)
      ·
        refine ⟨22221251545217886154782685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118513341574495392825507653 22221251545217886154782685)
        ·
          refine ⟨8332969329456707308043507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22221251545217886154782685 8332969329456707308043507)
          ·
            refine ⟨12499453994185060962065261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332969329456707308043507 12499453994185060962065261)
            ·
              refine ⟨4687295247819397860774473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12499453994185060962065261 4687295247819397860774473)
              ·
                refine ⟨3515471435864548395580855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687295247819397860774473 3515471435864548395580855)
                ·
                  refine ⟨5273207153796822593371283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515471435864548395580855 5273207153796822593371283)
                  ·
                    refine ⟨7909810730695233890056925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273207153796822593371283 7909810730695233890056925)
                    ·
                      refine ⟨2966179024010712708771347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909810730695233890056925 2966179024010712708771347)
                      ·
                        rfl

theorem cell23_5776613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5776613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776613 prefixEnd_5776613 := by exact prefixLift 5776613
  have htrace : WordTrace (prefixWord ++ tailWord_5776613) baseStart_5776613 baseEnd_5776613 := by
    simpa [prefixWord, tailWord_5776613, baseEnd_5776613] using wordTrace_append hprefix tailTrace_5776613
  have hstable : (prefixWord ++ tailWord_5776613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776613).length < 2 ^ (prefixWord ++ tailWord_5776613).sum := by decide
  have hdescent : baseEnd_5776613 < baseStart_5776613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776619 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 3, 2, 2]
def baseStart_5776619 : Nat := 118140960795 + 5776619 * 2 ^ 59
def prefixEnd_5776619 : Nat := 4983230072969 + 3 ^ 40 * 5776619 * 2
def baseEnd_5776619 : Nat := 2966182104894639685296319

theorem tailTrace_5776619 : CollatzResearch.WordTrace tailWord_5776619 prefixEnd_5776619 2966182104894639685296319 := by
  unfold tailWord_5776619
  simp only [CollatzResearch.WordTrace]
  refine ⟨210690603859303405825620911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140460402572868937217080607 210690603859303405825620911)
  ·
    refine ⟨316035905788955108738431367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210690603859303405825620911 316035905788955108738431367)
    ·
      refine ⟨474053858683432663107647051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316035905788955108738431367 474053858683432663107647051)
      ·
        refine ⟨711080788025148994661470577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474053858683432663107647051 711080788025148994661470577)
        ·
          refine ⟨533310591018861745996102933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711080788025148994661470577 533310591018861745996102933)
          ·
            refine ⟨24998933954009144343567325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 533310591018861745996102933 24998933954009144343567325)
            ·
              refine ⟨9374600232753429128837747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24998933954009144343567325 9374600232753429128837747)
              ·
                refine ⟨14061900349130143693256621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374600232753429128837747 14061900349130143693256621)
                ·
                  refine ⟨5273212630923803884971233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14061900349130143693256621 5273212630923803884971233)
                  ·
                    refine ⟨3954909473192852913728425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273212630923803884971233 3954909473192852913728425)
                    ·
                      refine ⟨2966182104894639685296319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954909473192852913728425 2966182104894639685296319)
                      ·
                        rfl

theorem cell23_5776619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 2, 2].length) (baseStart_5776619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776619 prefixEnd_5776619 := by exact prefixLift 5776619
  have htrace : WordTrace (prefixWord ++ tailWord_5776619) baseStart_5776619 baseEnd_5776619 := by
    simpa [prefixWord, tailWord_5776619, baseEnd_5776619] using wordTrace_append hprefix tailTrace_5776619
  have hstable : (prefixWord ++ tailWord_5776619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776619).length < 2 ^ (prefixWord ++ tailWord_5776619).sum := by decide
  have hdescent : baseEnd_5776619 < baseStart_5776619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776636 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_5776636 : Nat := 118140960795 + 5776636 * 2 ^ 59
def prefixEnd_5776636 : Nat := 4983230072969 + 3 ^ 40 * 5776636 * 2
def baseEnd_5776636 : Nat := 2966190834065766118783741

theorem tailTrace_5776636 : CollatzResearch.WordTrace tailWord_5776636 prefixEnd_5776636 2966190834065766118783741 := by
  unfold tailWord_5776636
  simp only [CollatzResearch.WordTrace]
  refine ⟨105345611950120908864494881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140460815933494545152659841 105345611950120908864494881)
  ·
    refine ⟨79009208962590681648371161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105345611950120908864494881 79009208962590681648371161)
    ·
      refine ⟨59256906721943011236278371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79009208962590681648371161 59256906721943011236278371)
      ·
        refine ⟨88885360082914516854417557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59256906721943011236278371 88885360082914516854417557)
        ·
          refine ⟨4166501253886617977550823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88885360082914516854417557 4166501253886617977550823)
          ·
            refine ⟨6249751880829926966326235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166501253886617977550823 6249751880829926966326235)
            ·
              refine ⟨9374627821244890449489353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249751880829926966326235 9374627821244890449489353)
              ·
                refine ⟨7030970865933667837117015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9374627821244890449489353 7030970865933667837117015)
                ·
                  refine ⟨10546456298900501755675523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7030970865933667837117015 10546456298900501755675523)
                  ·
                    refine ⟨15819684448350752633513285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10546456298900501755675523 15819684448350752633513285)
                    ·
                      refine ⟨2966190834065766118783741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15819684448350752633513285 2966190834065766118783741)
                      ·
                        rfl

theorem cell23_5776636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_5776636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776636 prefixEnd_5776636 := by exact prefixLift 5776636
  have htrace : WordTrace (prefixWord ++ tailWord_5776636) baseStart_5776636 baseEnd_5776636 := by
    simpa [prefixWord, tailWord_5776636, baseEnd_5776636] using wordTrace_append hprefix tailTrace_5776636
  have hstable : (prefixWord ++ tailWord_5776636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776636).length < 2 ^ (prefixWord ++ tailWord_5776636).sum := by decide
  have hdescent : baseEnd_5776636 < baseStart_5776636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776639 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_5776639 : Nat := 118140960795 + 5776639 * 2 ^ 59
def prefixEnd_5776639 : Nat := 4983230072969 + 3 ^ 40 * 5776639 * 2
def baseEnd_5776639 : Nat := 2966192374507729607046227

theorem tailTrace_5776639 : CollatzResearch.WordTrace tailWord_5776639 prefixEnd_5776639 2966192374507729607046227 := by
  unfold tailWord_5776639
  simp only [CollatzResearch.WordTrace]
  refine ⟨210691333319230949241348971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140460888879487299494232647 210691333319230949241348971)
  ·
    refine ⟨316036999978846423862023457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210691333319230949241348971 316036999978846423862023457)
    ·
      refine ⟨237027749984134817896517593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316036999978846423862023457 237027749984134817896517593)
      ·
        refine ⟨177770812488101113422388195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237027749984134817896517593 177770812488101113422388195)
        ·
          refine ⟨266656218732151670133582293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177770812488101113422388195 266656218732151670133582293)
          ·
            refine ⟨6249755126534804768755835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 266656218732151670133582293 6249755126534804768755835)
            ·
              refine ⟨9374632689802207153133753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249755126534804768755835 9374632689802207153133753)
              ·
                refine ⟨7030974517351655364850315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9374632689802207153133753 7030974517351655364850315)
                ·
                  refine ⟨10546461776027483047275473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7030974517351655364850315 10546461776027483047275473)
                  ·
                    refine ⟨7909846332020612285456605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10546461776027483047275473 7909846332020612285456605)
                    ·
                      refine ⟨2966192374507729607046227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909846332020612285456605 2966192374507729607046227)
                      ·
                        rfl

theorem cell23_5776639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_5776639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776639 prefixEnd_5776639 := by exact prefixLift 5776639
  have htrace : WordTrace (prefixWord ++ tailWord_5776639) baseStart_5776639 baseEnd_5776639 := by
    simpa [prefixWord, tailWord_5776639, baseEnd_5776639] using wordTrace_append hprefix tailTrace_5776639
  have hstable : (prefixWord ++ tailWord_5776639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776639).length < 2 ^ (prefixWord ++ tailWord_5776639).sum := by decide
  have hdescent : baseEnd_5776639 < baseStart_5776639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776652 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_5776652 : Nat := 118140960795 + 5776652 * 2 ^ 59
def prefixEnd_5776652 : Nat := 4983230072969 + 3 ^ 40 * 5776652 * 2
def baseEnd_5776652 : Nat := 2966199049756238056183667

theorem tailTrace_5776652 : CollatzResearch.WordTrace tailWord_5776652 prefixEnd_5776652 2966199049756238056183667 := by
  unfold tailWord_5776652
  simp only [CollatzResearch.WordTrace]
  refine ⟨105345903734091926230786105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140461204978789234974381473 105345903734091926230786105)
  ·
    refine ⟨79009427800568944673089579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105345903734091926230786105 79009427800568944673089579)
    ·
      refine ⟨118514141700853417009634369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79009427800568944673089579 118514141700853417009634369)
      ·
        refine ⟨88885606275640062757225777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118514141700853417009634369 88885606275640062757225777)
        ·
          refine ⟨66664204706730047067919333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88885606275640062757225777 66664204706730047067919333)
          ·
            refine ⟨12499538382511883825234875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66664204706730047067919333 12499538382511883825234875)
            ·
              refine ⟨18749307573767825737852313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12499538382511883825234875 18749307573767825737852313)
              ·
                refine ⟨14061980680325869303389235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18749307573767825737852313 14061980680325869303389235)
                ·
                  refine ⟨21092971020488803955083853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14061980680325869303389235 21092971020488803955083853)
                  ·
                    refine ⟨7909864132683301483156445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21092971020488803955083853 7909864132683301483156445)
                    ·
                      refine ⟨2966199049756238056183667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7909864132683301483156445 2966199049756238056183667)
                      ·
                        rfl

theorem cell23_5776652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_5776652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776652 prefixEnd_5776652 := by exact prefixLift 5776652
  have htrace : WordTrace (prefixWord ++ tailWord_5776652) baseStart_5776652 baseEnd_5776652 := by
    simpa [prefixWord, tailWord_5776652, baseEnd_5776652] using wordTrace_append hprefix tailTrace_5776652
  have hstable : (prefixWord ++ tailWord_5776652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776652).length < 2 ^ (prefixWord ++ tailWord_5776652).sum := by decide
  have hdescent : baseEnd_5776652 < baseStart_5776652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776675 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_5776675 : Nat := 118140960795 + 5776675 * 2 ^ 59
def prefixEnd_5776675 : Nat := 4983230072969 + 3 ^ 40 * 5776675 * 2
def baseEnd_5776675 : Nat := 2966210859811291466196061

theorem tailTrace_5776675 : CollatzResearch.WordTrace tailWord_5776675 prefixEnd_5776675 2966210859811291466196061 := by
  unfold tailWord_5776675
  simp only [CollatzResearch.WordTrace]
  refine ⟨210692646347100527389659479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140461764231400351593106319 210692646347100527389659479)
  ·
    refine ⟨316038969520650791084489219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210692646347100527389659479 316038969520650791084489219)
    ·
      refine ⟨474058454280976186626733829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316038969520650791084489219 474058454280976186626733829)
      ·
        refine ⟨88885960177683034992512593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 474058454280976186626733829 88885960177683034992512593)
        ·
          refine ⟨66664470133262276244384445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88885960177683034992512593 66664470133262276244384445)
          ·
            refine ⟨24999176299973353591644167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66664470133262276244384445 24999176299973353591644167)
            ·
              refine ⟨37498764449960030387466251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24999176299973353591644167 37498764449960030387466251)
              ·
                refine ⟨56248146674940045581199377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37498764449960030387466251 56248146674940045581199377)
                ·
                  refine ⟨42186110006205034185899533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56248146674940045581199377 42186110006205034185899533)
                  ·
                    refine ⟨15819791252326887819712325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42186110006205034185899533 15819791252326887819712325)
                    ·
                      refine ⟨2966210859811291466196061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15819791252326887819712325 2966210859811291466196061)
                      ·
                        rfl

theorem cell23_5776675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_5776675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776675 prefixEnd_5776675 := by exact prefixLift 5776675
  have htrace : WordTrace (prefixWord ++ tailWord_5776675) baseStart_5776675 baseEnd_5776675 := by
    simpa [prefixWord, tailWord_5776675, baseEnd_5776675] using wordTrace_append hprefix tailTrace_5776675
  have hstable : (prefixWord ++ tailWord_5776675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776675).length < 2 ^ (prefixWord ++ tailWord_5776675).sum := by decide
  have hdescent : baseEnd_5776675 < baseStart_5776675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776692 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_5776692 : Nat := 118140960795 + 5776692 * 2 ^ 59
def prefixEnd_5776692 : Nat := 4983230072969 + 3 ^ 40 * 5776692 * 2
def baseEnd_5776692 : Nat := 2966219588982417899683483

theorem tailTrace_5776692 : CollatzResearch.WordTrace tailWord_5776692 prefixEnd_5776692 2966219588982417899683483 := by
  unfold tailWord_5776692
  simp only [CollatzResearch.WordTrace]
  refine ⟨105346633194019469646514165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140462177592025959528685553 105346633194019469646514165)
  ·
    refine ⟨9876246861939325279360703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105346633194019469646514165 9876246861939325279360703)
    ·
      refine ⟨14814370292908987919041055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876246861939325279360703 14814370292908987919041055)
      ·
        refine ⟨22221555439363481878561583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814370292908987919041055 22221555439363481878561583)
        ·
          refine ⟨33332333159045222817842375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22221555439363481878561583 33332333159045222817842375)
          ·
            refine ⟨49998499738567834226763563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33332333159045222817842375 49998499738567834226763563)
            ·
              refine ⟨74997749607851751340145345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49998499738567834226763563 74997749607851751340145345)
              ·
                refine ⟨56248312205888813505109009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74997749607851751340145345 56248312205888813505109009)
                ·
                  refine ⟨42186234154416610128831757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56248312205888813505109009 42186234154416610128831757)
                  ·
                    refine ⟨15819837807906228798311909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42186234154416610128831757 15819837807906228798311909)
                    ·
                      refine ⟨2966219588982417899683483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15819837807906228798311909 2966219588982417899683483)
                      ·
                        rfl

theorem cell23_5776692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_5776692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776692 prefixEnd_5776692 := by exact prefixLift 5776692
  have htrace : WordTrace (prefixWord ++ tailWord_5776692) baseStart_5776692 baseEnd_5776692 := by
    simpa [prefixWord, tailWord_5776692, baseEnd_5776692] using wordTrace_append hprefix tailTrace_5776692
  have hstable : (prefixWord ++ tailWord_5776692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776692).length < 2 ^ (prefixWord ++ tailWord_5776692).sum := by decide
  have hdescent : baseEnd_5776692 < baseStart_5776692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776743 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_5776743 : Nat := 118140960795 + 5776743 * 2 ^ 59
def prefixEnd_5776743 : Nat := 4983230072969 + 3 ^ 40 * 5776743 * 2
def baseEnd_5776743 : Nat := 2966245776495797200145749

theorem tailTrace_5776743 : CollatzResearch.WordTrace tailWord_5776743 prefixEnd_5776743 2966245776495797200145749 := by
  unfold tailWord_5776743
  simp only [CollatzResearch.WordTrace]
  refine ⟨210695126510854175003134883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140463417673902783335423255 210695126510854175003134883)
  ·
    refine ⟨316042689766281262504702325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210695126510854175003134883 316042689766281262504702325)
    ·
      refine ⟨29629002165588868359815843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316042689766281262504702325 29629002165588868359815843)
      ·
        refine ⟨44443503248383302539723765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29629002165588868359815843 44443503248383302539723765)
        ·
          refine ⟨4166578429535934613099103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44443503248383302539723765 4166578429535934613099103)
          ·
            refine ⟨6249867644303901919648655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166578429535934613099103 6249867644303901919648655)
            ·
              refine ⟨9374801466455852879472983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249867644303901919648655 9374801466455852879472983)
              ·
                refine ⟨14062202199683779319209475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374801466455852879472983 14062202199683779319209475)
                ·
                  refine ⟨21093303299525668978814213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14062202199683779319209475 21093303299525668978814213)
                  ·
                    refine ⟨3954994368661062933527665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21093303299525668978814213 3954994368661062933527665)
                    ·
                      refine ⟨2966245776495797200145749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3954994368661062933527665 2966245776495797200145749)
                      ·
                        rfl

theorem cell23_5776743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_5776743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776743 prefixEnd_5776743 := by exact prefixLift 5776743
  have htrace : WordTrace (prefixWord ++ tailWord_5776743) baseStart_5776743 baseEnd_5776743 := by
    simpa [prefixWord, tailWord_5776743, baseEnd_5776743] using wordTrace_append hprefix tailTrace_5776743
  have hstable : (prefixWord ++ tailWord_5776743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776743).length < 2 ^ (prefixWord ++ tailWord_5776743).sum := by decide
  have hdescent : baseEnd_5776743 < baseStart_5776743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776745 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_5776745 : Nat := 118140960795 + 5776745 * 2 ^ 59
def prefixEnd_5776745 : Nat := 4983230072969 + 3 ^ 40 * 5776745 * 2
def baseEnd_5776745 : Nat := 988748934485702064106913

theorem tailTrace_5776745 : CollatzResearch.WordTrace tailWord_5776745 prefixEnd_5776745 988748934485702064106913 := by
  unfold tailWord_5776745
  simp only [CollatzResearch.WordTrace]
  refine ⟨210695199456846929344707689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140463466304564619563138459 210695199456846929344707689)
  ·
    refine ⟨158021399592635197008530767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210695199456846929344707689 158021399592635197008530767)
    ·
      refine ⟨237032099388952795512796151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158021399592635197008530767 237032099388952795512796151)
      ·
        refine ⟨355548149083429193269194227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237032099388952795512796151 355548149083429193269194227)
        ·
          refine ⟨533322223625143789903791341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355548149083429193269194227 533322223625143789903791341)
          ·
            refine ⟨199995833859428921213921753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533322223625143789903791341 199995833859428921213921753)
            ·
              refine ⟨149996875394571690910441315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199995833859428921213921753 149996875394571690910441315)
              ·
                refine ⟨224995313091857536365661973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149996875394571690910441315 224995313091857536365661973)
                ·
                  refine ⟨10546655301180822017140405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224995313091857536365661973 10546655301180822017140405)
                  ·
                    refine ⟨988748934485702064106913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10546655301180822017140405 988748934485702064106913)
                    ·
                      rfl

theorem cell23_5776745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_5776745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776745 prefixEnd_5776745 := by exact prefixLift 5776745
  have htrace : WordTrace (prefixWord ++ tailWord_5776745) baseStart_5776745 baseEnd_5776745 := by
    simpa [prefixWord, tailWord_5776745, baseEnd_5776745] using wordTrace_append hprefix tailTrace_5776745
  have hstable : (prefixWord ++ tailWord_5776745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776745).length < 2 ^ (prefixWord ++ tailWord_5776745).sum := by decide
  have hdescent : baseEnd_5776745 < baseStart_5776745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776785 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_5776785 : Nat := 118140960795 + 5776785 * 2 ^ 59
def prefixEnd_5776785 : Nat := 4983230072969 + 3 ^ 40 * 5776785 * 2
def baseEnd_5776785 : Nat := 2966267342683286035820555

theorem tailTrace_5776785 : CollatzResearch.WordTrace tailWord_5776785 prefixEnd_5776785 2966267342683286035820555 := by
  unfold tailWord_5776785
  simp only [CollatzResearch.WordTrace]
  refine ⟨210696658376702016176163809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140464438917801344117442539 210696658376702016176163809)
  ·
    refine ⟨158022493782526512132122857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210696658376702016176163809 158022493782526512132122857)
    ·
      refine ⟨118516870336894884099092143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158022493782526512132122857 118516870336894884099092143)
      ·
        refine ⟨177775305505342326148638215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118516870336894884099092143 177775305505342326148638215)
        ·
          refine ⟨266662958258013489222957323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177775305505342326148638215 266662958258013489222957323)
          ·
            refine ⟨399994437387020233834435985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266662958258013489222957323 399994437387020233834435985)
            ·
              refine ⟨299995828040265175375826989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399994437387020233834435985 299995828040265175375826989)
              ·
                refine ⟨112498435515099440765935121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 299995828040265175375826989 112498435515099440765935121)
                ·
                  refine ⟨84373826636324580574451341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112498435515099440765935121 84373826636324580574451341)
                  ·
                    refine ⟨31640184988621717715419253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84373826636324580574451341 31640184988621717715419253)
                    ·
                      refine ⟨2966267342683286035820555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31640184988621717715419253 2966267342683286035820555)
                      ·
                        rfl

theorem cell23_5776785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_5776785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776785 prefixEnd_5776785 := by exact prefixLift 5776785
  have htrace : WordTrace (prefixWord ++ tailWord_5776785) baseStart_5776785 baseEnd_5776785 := by
    simpa [prefixWord, tailWord_5776785, baseEnd_5776785] using wordTrace_append hprefix tailTrace_5776785
  have hstable : (prefixWord ++ tailWord_5776785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776785).length < 2 ^ (prefixWord ++ tailWord_5776785).sum := by decide
  have hdescent : baseEnd_5776785 < baseStart_5776785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776805 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 10]
def baseStart_5776805 : Nat := 118140960795 + 5776805 * 2 ^ 59
def prefixEnd_5776805 : Nat := 4983230072969 + 3 ^ 40 * 5776805 * 2
def baseEnd_5776805 : Nat := 329586401366263995285607

theorem tailTrace_5776805 : CollatzResearch.WordTrace tailWord_5776805 prefixEnd_5776805 329586401366263995285607 := by
  unfold tailWord_5776805
  simp only [CollatzResearch.WordTrace]
  refine ⟨210697387836629559591891869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140464925224419706394594579 210697387836629559591891869)
  ·
    refine ⟨79011520438736084846959451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210697387836629559591891869 79011520438736084846959451)
    ·
      refine ⟨118517280658104127270439177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79011520438736084846959451 118517280658104127270439177)
      ·
        refine ⟨88887960493578095452829383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118517280658104127270439177 88887960493578095452829383)
        ·
          refine ⟨133331940740367143179244075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88887960493578095452829383 133331940740367143179244075)
          ·
            refine ⟨199997911110550714768866113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133331940740367143179244075 199997911110550714768866113)
            ·
              refine ⟨149998433332913036076649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199997911110550714768866113 149998433332913036076649585)
              ·
                refine ⟨112498824999684777057487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149998433332913036076649585 112498824999684777057487189)
                ·
                  refine ⟨329586401366263995285607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112498824999684777057487189 329586401366263995285607)
                  ·
                    rfl

theorem cell23_5776805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_5776805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776805 prefixEnd_5776805 := by exact prefixLift 5776805
  have htrace : WordTrace (prefixWord ++ tailWord_5776805) baseStart_5776805 baseEnd_5776805 := by
    simpa [prefixWord, tailWord_5776805, baseEnd_5776805] using wordTrace_append hprefix tailTrace_5776805
  have hstable : (prefixWord ++ tailWord_5776805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776805).length < 2 ^ (prefixWord ++ tailWord_5776805).sum := by decide
  have hdescent : baseEnd_5776805 < baseStart_5776805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776834 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_5776834 : Nat := 118140960795 + 5776834 * 2 ^ 59
def prefixEnd_5776834 : Nat := 4983230072969 + 3 ^ 40 * 5776834 * 2
def baseEnd_5776834 : Nat := 329588055915039593789759

theorem tailTrace_5776834 : CollatzResearch.WordTrace tailWord_5776834 prefixEnd_5776834 329588055915039593789759 := by
  unfold tailWord_5776834
  simp only [CollatzResearch.WordTrace]
  refine ⟨52674611388381124386174389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140465630369016331696465037 52674611388381124386174389)
  ·
    refine ⟨4938244817660730411203849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52674611388381124386174389 4938244817660730411203849)
    ·
      refine ⟨3703683613245547808402887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4938244817660730411203849 3703683613245547808402887)
      ·
        refine ⟨5555525419868321712604331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703683613245547808402887 5555525419868321712604331)
        ·
          refine ⟨8333288129802482568906497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555525419868321712604331 8333288129802482568906497)
          ·
            refine ⟨6249966097351861926679873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8333288129802482568906497 6249966097351861926679873)
            ·
              refine ⟨4687474573013896445009905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6249966097351861926679873 4687474573013896445009905)
              ·
                refine ⟨3515605929760422333757429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687474573013896445009905 3515605929760422333757429)
                ·
                  refine ⟨329588055915039593789759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515605929760422333757429 329588055915039593789759)
                  ·
                    rfl

theorem cell23_5776834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_5776834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776834 prefixEnd_5776834 := by exact prefixLift 5776834
  have htrace : WordTrace (prefixWord ++ tailWord_5776834) baseStart_5776834 baseEnd_5776834 := by
    simpa [prefixWord, tailWord_5776834, baseEnd_5776834] using wordTrace_append hprefix tailTrace_5776834
  have hstable : (prefixWord ++ tailWord_5776834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776834).length < 2 ^ (prefixWord ++ tailWord_5776834).sum := by decide
  have hdescent : baseEnd_5776834 < baseStart_5776834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776836 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_5776836 : Nat := 118140960795 + 5776836 * 2 ^ 59
def prefixEnd_5776836 : Nat := 4983230072969 + 3 ^ 40 * 5776836 * 2
def baseEnd_5776836 : Nat := 2966293530196665336282821

theorem tailTrace_5776836 : CollatzResearch.WordTrace tailWord_5776836 prefixEnd_5776836 2966293530196665336282821 := by
  unfold tailWord_5776836
  simp only [CollatzResearch.WordTrace]
  refine ⟨105349259249758625943135181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140465678999678167924180241 105349259249758625943135181)
  ·
    refine ⟨39505972218659484728675693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105349259249758625943135181 39505972218659484728675693)
    ·
      refine ⟨14814739581997306773253385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39505972218659484728675693 14814739581997306773253385)
      ·
        refine ⟨11111054686497980079940039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14814739581997306773253385 11111054686497980079940039)
        ·
          refine ⟨16666582029746970119910059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111054686497980079940039 16666582029746970119910059)
          ·
            refine ⟨24999873044620455179865089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16666582029746970119910059 24999873044620455179865089)
            ·
              refine ⟨18749904783465341384898817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24999873044620455179865089 18749904783465341384898817)
              ·
                refine ⟨14062428587599006038674113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18749904783465341384898817 14062428587599006038674113)
                ·
                  refine ⟨10546821440699254529005585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14062428587599006038674113 10546821440699254529005585)
                  ·
                    refine ⟨7910116080524440896754189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10546821440699254529005585 7910116080524440896754189)
                    ·
                      refine ⟨2966293530196665336282821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7910116080524440896754189 2966293530196665336282821)
                      ·
                        rfl

theorem cell23_5776836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_5776836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776836 prefixEnd_5776836 := by exact prefixLift 5776836
  have htrace : WordTrace (prefixWord ++ tailWord_5776836) baseStart_5776836 baseEnd_5776836 := by
    simpa [prefixWord, tailWord_5776836, baseEnd_5776836] using wordTrace_append hprefix tailTrace_5776836
  have hstable : (prefixWord ++ tailWord_5776836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776836).length < 2 ^ (prefixWord ++ tailWord_5776836).sum := by decide
  have hdescent : baseEnd_5776836 < baseStart_5776836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776869 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_5776869 : Nat := 118140960795 + 5776869 * 2 ^ 59
def prefixEnd_5776869 : Nat := 4983230072969 + 3 ^ 40 * 5776869 * 2
def baseEnd_5776869 : Nat := 988770158352754569056723

theorem tailTrace_5776869 : CollatzResearch.WordTrace tailWord_5776869 prefixEnd_5776869 988770158352754569056723 := by
  unfold tailWord_5776869
  simp only [CollatzResearch.WordTrace]
  refine ⟨210699722108397698522221661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140466481405598465681481107 210699722108397698522221661)
  ·
    refine ⟨79012395790649136945833123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210699722108397698522221661 79012395790649136945833123)
    ·
      refine ⟨118518593685973705418749685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79012395790649136945833123 118518593685973705418749685)
      ·
        refine ⟨11111118158060034883007783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118518593685973705418749685 11111118158060034883007783)
        ·
          refine ⟨16666677237090052324511675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111118158060034883007783 16666677237090052324511675)
          ·
            refine ⟨25000015855635078486767513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16666677237090052324511675 25000015855635078486767513)
            ·
              refine ⟨18750011891726308865075635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25000015855635078486767513 18750011891726308865075635)
              ·
                refine ⟨28125017837589463297613453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18750011891726308865075635 28125017837589463297613453)
                ·
                  refine ⟨10546881689096048736605045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28125017837589463297613453 10546881689096048736605045)
                  ·
                    refine ⟨988770158352754569056723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10546881689096048736605045 988770158352754569056723)
                    ·
                      rfl

theorem cell23_5776869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_5776869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776869 prefixEnd_5776869 := by exact prefixLift 5776869
  have htrace : WordTrace (prefixWord ++ tailWord_5776869) baseStart_5776869 baseEnd_5776869 := by
    simpa [prefixWord, tailWord_5776869, baseEnd_5776869] using wordTrace_append hprefix tailTrace_5776869
  have hstable : (prefixWord ++ tailWord_5776869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776869).length < 2 ^ (prefixWord ++ tailWord_5776869).sum := by decide
  have hdescent : baseEnd_5776869 < baseStart_5776869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776886 : List Nat := [5, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5776886 : Nat := 118140960795 + 5776886 * 2 ^ 59
def prefixEnd_5776886 : Nat := 4983230072969 + 3 ^ 40 * 5776886 * 2
def baseEnd_5776886 : Nat := 988773068076463380219197

theorem tailTrace_5776886 : CollatzResearch.WordTrace tailWord_5776886 prefixEnd_5776886 988773068076463380219197 := by
  unfold tailWord_5776886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13168771384333506901599407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140466894766224073617060341 13168771384333506901599407)
  ·
    refine ⟨19753157076500260352399111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13168771384333506901599407 19753157076500260352399111)
    ·
      refine ⟨29629735614750390528598667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19753157076500260352399111 29629735614750390528598667)
      ·
        refine ⟨44444603422125585792898001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29629735614750390528598667 44444603422125585792898001)
        ·
          refine ⟨33333452566594189344673501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44444603422125585792898001 33333452566594189344673501)
          ·
            refine ⟨12500044712472821004252563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33333452566594189344673501 12500044712472821004252563)
            ·
              refine ⟨18750067068709231506378845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12500044712472821004252563 18750067068709231506378845)
              ·
                refine ⟨7031275150765961814892067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18750067068709231506378845 7031275150765961814892067)
                ·
                  refine ⟨10546912726148942722338101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7031275150765961814892067 10546912726148942722338101)
                  ·
                    refine ⟨988773068076463380219197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10546912726148942722338101 988773068076463380219197)
                    ·
                      rfl

theorem cell23_5776886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5776886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776886 prefixEnd_5776886 := by exact prefixLift 5776886
  have htrace : WordTrace (prefixWord ++ tailWord_5776886) baseStart_5776886 baseEnd_5776886 := by
    simpa [prefixWord, tailWord_5776886, baseEnd_5776886] using wordTrace_append hprefix tailTrace_5776886
  have hstable : (prefixWord ++ tailWord_5776886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776886).length < 2 ^ (prefixWord ++ tailWord_5776886).sum := by decide
  have hdescent : baseEnd_5776886 < baseStart_5776886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776899 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 2, 4]
def baseStart_5776899 : Nat := 118140960795 + 5776899 * 2 ^ 59
def prefixEnd_5776899 : Nat := 4983230072969 + 3 ^ 40 * 5776899 * 2
def baseEnd_5776899 : Nat := 988775293159299529931677

theorem tailTrace_5776899 : CollatzResearch.WordTrace tailWord_5776899 prefixEnd_5776899 988775293159299529931677 := by
  unfold tailWord_5776899
  simp only [CollatzResearch.WordTrace]
  refine ⟨210700816298289013645813751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140467210865526009097209167 210700816298289013645813751)
  ·
    refine ⟨316051224447433520468720627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210700816298289013645813751 316051224447433520468720627)
    ·
      refine ⟨474076836671150280703080941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316051224447433520468720627 474076836671150280703080941)
      ·
        refine ⟨177778813751681355263655353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474076836671150280703080941 177778813751681355263655353)
        ·
          refine ⟨133334110313761016447741515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177778813751681355263655353 133334110313761016447741515)
          ·
            refine ⟨200001165470641524671612273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133334110313761016447741515 200001165470641524671612273)
            ·
              refine ⟨150000874102981143503709205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200001165470641524671612273 150000874102981143503709205)
              ·
                refine ⟨7031290973577241101736369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150000874102981143503709205 7031290973577241101736369)
                ·
                  refine ⟨5273468230182930826302277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031290973577241101736369 5273468230182930826302277)
                  ·
                    refine ⟨988775293159299529931677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5273468230182930826302277 988775293159299529931677)
                    ·
                      rfl

theorem cell23_5776899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 2, 4].length) (baseStart_5776899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776899 prefixEnd_5776899 := by exact prefixLift 5776899
  have htrace : WordTrace (prefixWord ++ tailWord_5776899) baseStart_5776899 baseEnd_5776899 := by
    simpa [prefixWord, tailWord_5776899, baseEnd_5776899] using wordTrace_append hprefix tailTrace_5776899
  have hstable : (prefixWord ++ tailWord_5776899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776899).length < 2 ^ (prefixWord ++ tailWord_5776899).sum := by decide
  have hdescent : baseEnd_5776899 < baseStart_5776899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776929 : List Nat := [1, 2, 3, 2, 2, 2, 4, 7]
def baseStart_5776929 : Nat := 118140960795 + 5776929 * 2 ^ 59
def prefixEnd_5776929 : Nat := 4983230072969 + 3 ^ 40 * 5776929 * 2
def baseEnd_5776929 : Nat := 109864491996204943422959

theorem tailTrace_5776929 : CollatzResearch.WordTrace tailWord_5776929 prefixEnd_5776929 109864491996204943422959 := by
  unfold tailWord_5776929
  simp only [CollatzResearch.WordTrace]
  refine ⟨210701910488180328769405841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140467940325453552512937227 210701910488180328769405841)
  ·
    refine ⟨158026432866135246577054381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210701910488180328769405841 158026432866135246577054381)
    ·
      refine ⟨59259912324800717466395393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158026432866135246577054381 59259912324800717466395393)
      ·
        refine ⟨44444934243600538099796545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59259912324800717466395393 44444934243600538099796545)
        ·
          refine ⟨33333700682700403574847409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44444934243600538099796545 33333700682700403574847409)
          ·
            refine ⟨25000275512025302681135557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33333700682700403574847409 25000275512025302681135557)
            ·
              refine ⟨4687551658504744252712917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25000275512025302681135557 4687551658504744252712917)
              ·
                refine ⟨109864491996204943422959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4687551658504744252712917 109864491996204943422959)
                ·
                  rfl

theorem cell23_5776929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 7].length) (baseStart_5776929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776929 prefixEnd_5776929 := by exact prefixLift 5776929
  have htrace : WordTrace (prefixWord ++ tailWord_5776929) baseStart_5776929 baseEnd_5776929 := by
    simpa [prefixWord, tailWord_5776929, baseEnd_5776929] using wordTrace_append hprefix tailTrace_5776929
  have hstable : (prefixWord ++ tailWord_5776929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776929).length < 2 ^ (prefixWord ++ tailWord_5776929).sum := by decide
  have hdescent : baseEnd_5776929 < baseStart_5776929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776957 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_5776957 : Nat := 118140960795 + 5776957 * 2 ^ 59
def prefixEnd_5776957 : Nat := 4983230072969 + 3 ^ 40 * 5776957 * 2
def baseEnd_5776957 : Nat := 2966355661355859362869765

theorem tailTrace_5776957 : CollatzResearch.WordTrace tailWord_5776957 prefixEnd_5776957 2966355661355859362869765 := by
  unfold tailWord_5776957
  simp only [CollatzResearch.WordTrace]
  refine ⟨210702931732078889551425125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140468621154719259700950083 210702931732078889551425125)
  ·
    refine ⟨39506799699764791790892211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210702931732078889551425125 39506799699764791790892211)
    ·
      refine ⟨59260199549647187686338317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39506799699764791790892211 59260199549647187686338317)
      ·
        refine ⟨22222574831117695382376869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59260199549647187686338317 22222574831117695382376869)
        ·
          refine ⟨4166732780834567884195663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22222574831117695382376869 4166732780834567884195663)
          ·
            refine ⟨6250099171251851826293495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166732780834567884195663 6250099171251851826293495)
            ·
              refine ⟨9375148756877777739440243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250099171251851826293495 9375148756877777739440243)
              ·
                refine ⟨14062723135316666609160365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375148756877777739440243 14062723135316666609160365)
                ·
                  refine ⟨5273521175743749978435137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14062723135316666609160365 5273521175743749978435137)
                  ·
                    refine ⟨3955140881807812483826353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273521175743749978435137 3955140881807812483826353)
                    ·
                      refine ⟨2966355661355859362869765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955140881807812483826353 2966355661355859362869765)
                      ·
                        rfl

theorem cell23_5776957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_5776957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776957 prefixEnd_5776957 := by exact prefixLift 5776957
  have htrace : WordTrace (prefixWord ++ tailWord_5776957) baseStart_5776957 baseEnd_5776957 := by
    simpa [prefixWord, tailWord_5776957, baseEnd_5776957] using wordTrace_append hprefix tailTrace_5776957
  have hstable : (prefixWord ++ tailWord_5776957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776957).length < 2 ^ (prefixWord ++ tailWord_5776957).sum := by decide
  have hdescent : baseEnd_5776957 < baseStart_5776957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776983 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_5776983 : Nat := 118140960795 + 5776983 * 2 ^ 59
def prefixEnd_5776983 : Nat := 4983230072969 + 3 ^ 40 * 5776983 * 2
def baseEnd_5776983 : Nat := 2966369011852876261144645

theorem tailTrace_5776983 : CollatzResearch.WordTrace tailWord_5776983 prefixEnd_5776983 2966369011852876261144645 := by
  unfold tailWord_5776983
  simp only [CollatzResearch.WordTrace]
  refine ⟨210703880029984695991871603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140469253353323130661247735 210703880029984695991871603)
  ·
    refine ⟨316055820044977043987807405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210703880029984695991871603 316055820044977043987807405)
    ·
      refine ⟨118520932516866391495427777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316055820044977043987807405 118520932516866391495427777)
      ·
        refine ⟨88890699387649793621570833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118520932516866391495427777 88890699387649793621570833)
        ·
          refine ⟨66668024540737345216178125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88890699387649793621570833 66668024540737345216178125)
          ·
            refine ⟨25000509202776504456066797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66668024540737345216178125 25000509202776504456066797)
            ·
              refine ⟨9375190951041189171025049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25000509202776504456066797 9375190951041189171025049)
              ·
                refine ⟨7031393213280891878268787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9375190951041189171025049 7031393213280891878268787)
                ·
                  refine ⟨10547089819921337817403181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7031393213280891878268787 10547089819921337817403181)
                  ·
                    refine ⟨3955158682470501681526193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10547089819921337817403181 3955158682470501681526193)
                    ·
                      refine ⟨2966369011852876261144645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955158682470501681526193 2966369011852876261144645)
                      ·
                        rfl

theorem cell23_5776983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_5776983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776983 prefixEnd_5776983 := by exact prefixLift 5776983
  have htrace : WordTrace (prefixWord ++ tailWord_5776983) baseStart_5776983 baseEnd_5776983 := by
    simpa [prefixWord, tailWord_5776983, baseEnd_5776983] using wordTrace_append hprefix tailTrace_5776983
  have hstable : (prefixWord ++ tailWord_5776983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776983).length < 2 ^ (prefixWord ++ tailWord_5776983).sum := by decide
  have hdescent : baseEnd_5776983 < baseStart_5776983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776996 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 4, 2]
def baseStart_5776996 : Nat := 118140960795 + 5776996 * 2 ^ 59
def prefixEnd_5776996 : Nat := 4983230072969 + 3 ^ 40 * 5776996 * 2
def baseEnd_5776996 : Nat := 2966375687101384710282085

theorem tailTrace_5776996 : CollatzResearch.WordTrace tailWord_5776996 prefixEnd_5776996 2966375687101384710282085 := by
  unfold tailWord_5776996
  simp only [CollatzResearch.WordTrace]
  refine ⟨105352177089468799606047421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140469569452625066141396561 105352177089468799606047421)
  ·
    refine ⟨39507066408550799852267783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105352177089468799606047421 39507066408550799852267783)
    ·
      refine ⟨59260599612826199778401675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39507066408550799852267783 59260599612826199778401675)
      ·
        refine ⟨88890899419239299667602513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59260599612826199778401675 88890899419239299667602513)
        ·
          refine ⟨66668174564429474750701885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88890899419239299667602513 66668174564429474750701885)
          ·
            refine ⟨25000565461661053031513207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66668174564429474750701885 25000565461661053031513207)
            ·
              refine ⟨37500848192491579547269811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25000565461661053031513207 37500848192491579547269811)
              ·
                refine ⟨56251272288737369320904717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37500848192491579547269811 56251272288737369320904717)
                ·
                  refine ⟨21094227108276513495339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56251272288737369320904717 21094227108276513495339269)
                  ·
                    refine ⟨3955167582801846280376113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21094227108276513495339269 3955167582801846280376113)
                    ·
                      refine ⟨2966375687101384710282085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955167582801846280376113 2966375687101384710282085)
                      ·
                        rfl

theorem cell23_5776996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_5776996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776996 prefixEnd_5776996 := by exact prefixLift 5776996
  have htrace : WordTrace (prefixWord ++ tailWord_5776996) baseStart_5776996 baseEnd_5776996 := by
    simpa [prefixWord, tailWord_5776996, baseEnd_5776996] using wordTrace_append hprefix tailTrace_5776996
  have hstable : (prefixWord ++ tailWord_5776996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776996).length < 2 ^ (prefixWord ++ tailWord_5776996).sum := by decide
  have hdescent : baseEnd_5776996 < baseStart_5776996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5776999 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_5776999 : Nat := 118140960795 + 5776999 * 2 ^ 59
def prefixEnd_5776999 : Nat := 4983230072969 + 3 ^ 40 * 5776999 * 2
def baseEnd_5776999 : Nat := 2966377227543348198544571

theorem tailTrace_5776999 : CollatzResearch.WordTrace tailWord_5776999 prefixEnd_5776999 2966377227543348198544571 := by
  unfold tailWord_5776999
  simp only [CollatzResearch.WordTrace]
  refine ⟨210704463597926730724454051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140469642398617820482969367 210704463597926730724454051)
  ·
    refine ⟨316056695396890096086681077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210704463597926730724454051 316056695396890096086681077)
    ·
      refine ⟨29630315193458446508126351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316056695396890096086681077 29630315193458446508126351)
      ·
        refine ⟨44445472790187669762189527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29630315193458446508126351 44445472790187669762189527)
        ·
          refine ⟨66668209185281504643284291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44445472790187669762189527 66668209185281504643284291)
          ·
            refine ⟨100002313777922256964926437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66668209185281504643284291 100002313777922256964926437)
            ·
              refine ⟨18750433833360423180923707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100002313777922256964926437 18750433833360423180923707)
              ·
                refine ⟨28125650750040634771385561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18750433833360423180923707 28125650750040634771385561)
                ·
                  refine ⟨21094238062530476078539171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28125650750040634771385561 21094238062530476078539171)
                  ·
                    refine ⟨31641357093795714117808757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21094238062530476078539171 31641357093795714117808757)
                    ·
                      refine ⟨2966377227543348198544571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31641357093795714117808757 2966377227543348198544571)
                      ·
                        rfl

theorem cell23_5776999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_5776999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5776999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5776999 prefixEnd_5776999 := by exact prefixLift 5776999
  have htrace : WordTrace (prefixWord ++ tailWord_5776999) baseStart_5776999 baseEnd_5776999 := by
    simpa [prefixWord, tailWord_5776999, baseEnd_5776999] using wordTrace_append hprefix tailTrace_5776999
  have hstable : (prefixWord ++ tailWord_5776999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5776999).length < 2 ^ (prefixWord ++ tailWord_5776999).sum := by decide
  have hdescent : baseEnd_5776999 < baseStart_5776999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5776999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777049 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_5777049 : Nat := 118140960795 + 5777049 * 2 ^ 59
def prefixEnd_5777049 : Nat := 4983230072969 + 3 ^ 40 * 5777049 * 2
def baseEnd_5777049 : Nat := 988800967192024334306447

theorem tailTrace_5777049 : CollatzResearch.WordTrace tailWord_5777049 prefixEnd_5777049 988800967192024334306447 := by
  unfold tailWord_5777049
  simp only [CollatzResearch.WordTrace]
  refine ⟨210706287247745589263774201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140470858165163726175849467 210706287247745589263774201)
  ·
    refine ⟨158029715435809191947830651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210706287247745589263774201 158029715435809191947830651)
    ·
      refine ⟨237044573153713787921745977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158029715435809191947830651 237044573153713787921745977)
      ·
        refine ⟨177783429865285340941309483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237044573153713787921745977 177783429865285340941309483)
        ·
          refine ⟨266675144797928011411964225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177783429865285340941309483 266675144797928011411964225)
          ·
            refine ⟨200006358598446008558973169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266675144797928011411964225 200006358598446008558973169)
            ·
              refine ⟨150004768948834506419229877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200006358598446008558973169 150004768948834506419229877)
              ·
                refine ⟨14062947088953234976802801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150004768948834506419229877 14062947088953234976802801)
                ·
                  refine ⟨10547210316714926232602101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14062947088953234976802801 10547210316714926232602101)
                  ·
                    refine ⟨988800967192024334306447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10547210316714926232602101 988800967192024334306447)
                    ·
                      rfl

theorem cell23_5777049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_5777049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777049 prefixEnd_5777049 := by exact prefixLift 5777049
  have htrace : WordTrace (prefixWord ++ tailWord_5777049) baseStart_5777049 baseEnd_5777049 := by
    simpa [prefixWord, tailWord_5777049, baseEnd_5777049] using wordTrace_append hprefix tailTrace_5777049
  have hstable : (prefixWord ++ tailWord_5777049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777049).length < 2 ^ (prefixWord ++ tailWord_5777049).sum := by decide
  have hdescent : baseEnd_5777049 < baseStart_5777049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777064 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5777064 : Nat := 118140960795 + 5777064 * 2 ^ 59
def prefixEnd_5777064 : Nat := 4983230072969 + 3 ^ 40 * 5777064 * 2
def baseEnd_5777064 : Nat := 2966410603785890444231773

theorem tailTrace_5777064 : CollatzResearch.WordTrace tailWord_5777064 prefixEnd_5777064 2966410603785890444231773 := by
  unfold tailWord_5777064
  simp only [CollatzResearch.WordTrace]
  refine ⟨105353417171345623412785123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140471222895127497883713497 105353417171345623412785123)
  ·
    refine ⟨158030125757018435119177685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105353417171345623412785123 158030125757018435119177685)
    ·
      refine ⟨3703831072430119573105727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 158030125757018435119177685 3703831072430119573105727)
      ·
        refine ⟨5555746608645179359658591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703831072430119573105727 5555746608645179359658591)
        ·
          refine ⟨8333619912967769039487887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555746608645179359658591 8333619912967769039487887)
          ·
            refine ⟨12500429869451653559231831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333619912967769039487887 12500429869451653559231831)
            ·
              refine ⟨18750644804177480338847747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12500429869451653559231831 18750644804177480338847747)
              ·
                refine ⟨28125967206266220508271621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18750644804177480338847747 28125967206266220508271621)
                ·
                  refine ⟨5273618851174916345300929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28125967206266220508271621 5273618851174916345300929)
                  ·
                    refine ⟨3955214138381187258975697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273618851174916345300929 3955214138381187258975697)
                    ·
                      refine ⟨2966410603785890444231773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955214138381187258975697 2966410603785890444231773)
                      ·
                        rfl

theorem cell23_5777064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5777064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777064 prefixEnd_5777064 := by exact prefixLift 5777064
  have htrace : WordTrace (prefixWord ++ tailWord_5777064) baseStart_5777064 baseEnd_5777064 := by
    simpa [prefixWord, tailWord_5777064, baseEnd_5777064] using wordTrace_append hprefix tailTrace_5777064
  have hstable : (prefixWord ++ tailWord_5777064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777064).length < 2 ^ (prefixWord ++ tailWord_5777064).sum := by decide
  have hdescent : baseEnd_5777064 < baseStart_5777064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777086 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5777086 : Nat := 118140960795 + 5777086 * 2 ^ 59
def prefixEnd_5777086 : Nat := 4983230072969 + 3 ^ 40 * 5777086 * 2
def baseEnd_5777086 : Nat := 2966421900360289358156671

theorem tailTrace_5777086 : CollatzResearch.WordTrace tailWord_5777086 prefixEnd_5777086 2966421900360289358156671 := by
  unfold tailWord_5777086
  simp only [CollatzResearch.WordTrace]
  refine ⟨26338454593576443072858889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140471757832407696388580741 26338454593576443072858889)
  ·
    refine ⟨19753840945182332304644167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26338454593576443072858889 19753840945182332304644167)
    ·
      refine ⟨29630761417773498456966251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19753840945182332304644167 29630761417773498456966251)
      ·
        refine ⟨44446142126660247685449377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29630761417773498456966251 44446142126660247685449377)
        ·
          refine ⟨33334606594995185764087033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44446142126660247685449377 33334606594995185764087033)
          ·
            refine ⟨25000954946246389323065275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33334606594995185764087033 25000954946246389323065275)
            ·
              refine ⟨37501432419369583984597913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25000954946246389323065275 37501432419369583984597913)
              ·
                refine ⟨28126074314527187988448435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37501432419369583984597913 28126074314527187988448435)
                ·
                  refine ⟨42189111471790781982672653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28126074314527187988448435 42189111471790781982672653)
                  ·
                    refine ⟨15820916801921543243502245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42189111471790781982672653 15820916801921543243502245)
                    ·
                      refine ⟨2966421900360289358156671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15820916801921543243502245 2966421900360289358156671)
                      ·
                        rfl

theorem cell23_5777086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5777086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777086 prefixEnd_5777086 := by exact prefixLift 5777086
  have htrace : WordTrace (prefixWord ++ tailWord_5777086) baseStart_5777086 baseEnd_5777086 := by
    simpa [prefixWord, tailWord_5777086, baseEnd_5777086] using wordTrace_append hprefix tailTrace_5777086
  have hstable : (prefixWord ++ tailWord_5777086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777086).length < 2 ^ (prefixWord ++ tailWord_5777086).sum := by decide
  have hdescent : baseEnd_5777086 < baseStart_5777086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777096 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 3, 4]
def baseStart_5777096 : Nat := 118140960795 + 5777096 * 2 ^ 59
def prefixEnd_5777096 : Nat := 4983230072969 + 3 ^ 40 * 5777096 * 2
def baseEnd_5777096 : Nat := 988809011722278106343875

theorem tailTrace_5777096 : CollatzResearch.WordTrace tailWord_5777096 prefixEnd_5777096 988809011722278106343875 := by
  unfold tailWord_5777096
  simp only [CollatzResearch.WordTrace]
  refine ⟨105354000739287658145367571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140472000985716877527156761 105354000739287658145367571)
  ·
    refine ⟨158031001108931487218051357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105354000739287658145367571 158031001108931487218051357)
    ·
      refine ⟨59261625415849307706769259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158031001108931487218051357 59261625415849307706769259)
      ·
        refine ⟨88892438123773961560153889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59261625415849307706769259 88892438123773961560153889)
        ·
          refine ⟨66669328592830471170115417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88892438123773961560153889 66669328592830471170115417)
          ·
            refine ⟨50001996444622853377586563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66669328592830471170115417 50001996444622853377586563)
            ·
              refine ⟨75002994666934280066379845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50001996444622853377586563 75002994666934280066379845)
              ·
                refine ⟨14063061500050177512446221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75002994666934280066379845 14063061500050177512446221)
                ·
                  refine ⟨5273648062518816567167333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14063061500050177512446221 5273648062518816567167333)
                  ·
                    refine ⟨988809011722278106343875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5273648062518816567167333 988809011722278106343875)
                    ·
                      rfl

theorem cell23_5777096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_5777096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777096 prefixEnd_5777096 := by exact prefixLift 5777096
  have htrace : WordTrace (prefixWord ++ tailWord_5777096) baseStart_5777096 baseEnd_5777096 := by
    simpa [prefixWord, tailWord_5777096, baseEnd_5777096] using wordTrace_append hprefix tailTrace_5777096
  have hstable : (prefixWord ++ tailWord_5777096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777096).length < 2 ^ (prefixWord ++ tailWord_5777096).sum := by decide
  have hdescent : baseEnd_5777096 < baseStart_5777096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777149 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_5777149 : Nat := 118140960795 + 5777149 * 2 ^ 59
def prefixEnd_5777149 : Nat := 4983230072969 + 3 ^ 40 * 5777149 * 2
def baseEnd_5777149 : Nat := 2966454249641522611668881

theorem tailTrace_5777149 : CollatzResearch.WordTrace tailWord_5777149 prefixEnd_5777149 2966454249641522611668881 := by
  unfold tailWord_5777149
  simp only [CollatzResearch.WordTrace]
  refine ⟨210709934547383306342414501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140473289698255537561609667 210709934547383306342414501)
  ·
    refine ⟨39508112727634369939202719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210709934547383306342414501 39508112727634369939202719)
    ·
      refine ⟨59262169091451554908804079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39508112727634369939202719 59262169091451554908804079)
      ·
        refine ⟨88893253637177332363206119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59262169091451554908804079 88893253637177332363206119)
        ·
          refine ⟨133339880455765998544809179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88893253637177332363206119 133339880455765998544809179)
          ·
            refine ⟨200009820683648997817213769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133339880455765998544809179 200009820683648997817213769)
            ·
              refine ⟨150007365512736748362910327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200009820683648997817213769 150007365512736748362910327)
              ·
                refine ⟨225011048269105122544365491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150007365512736748362910327 225011048269105122544365491)
                ·
                  refine ⟨337516572403657683816548237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225011048269105122544365491 337516572403657683816548237)
                  ·
                    refine ⟨126568714651371631431205589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 337516572403657683816548237 126568714651371631431205589)
                    ·
                      refine ⟨2966454249641522611668881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126568714651371631431205589 2966454249641522611668881)
                      ·
                        rfl

theorem cell23_5777149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_5777149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777149 prefixEnd_5777149 := by exact prefixLift 5777149
  have htrace : WordTrace (prefixWord ++ tailWord_5777149) baseStart_5777149 baseEnd_5777149 := by
    simpa [prefixWord, tailWord_5777149, baseEnd_5777149] using wordTrace_append hprefix tailTrace_5777149
  have hstable : (prefixWord ++ tailWord_5777149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777149).length < 2 ^ (prefixWord ++ tailWord_5777149).sum := by decide
  have hdescent : baseEnd_5777149 < baseStart_5777149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777153 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_5777153 : Nat := 118140960795 + 5777153 * 2 ^ 59
def prefixEnd_5777153 : Nat := 4983230072969 + 3 ^ 40 * 5777153 * 2
def baseEnd_5777153 : Nat := 2966456303564140596018863

theorem tailTrace_5777153 : CollatzResearch.WordTrace tailWord_5777153 prefixEnd_5777153 2966456303564140596018863 := by
  unfold tailWord_5777153
  simp only [CollatzResearch.WordTrace]
  refine ⟨210710080439368815025560113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140473386959579210017040075 210710080439368815025560113)
  ·
    refine ⟨158032560329526611269170085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210710080439368815025560113 158032560329526611269170085)
    ·
      refine ⟨29631105061786239612969391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158032560329526611269170085 29631105061786239612969391)
      ·
        refine ⟨44446657592679359419454087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29631105061786239612969391 44446657592679359419454087)
        ·
          refine ⟨66669986389019039129181131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44446657592679359419454087 66669986389019039129181131)
          ·
            refine ⟨100004979583528558693771697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66669986389019039129181131 100004979583528558693771697)
            ·
              refine ⟨75003734687646419020328773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100004979583528558693771697 75003734687646419020328773)
              ·
                refine ⟨14063200253933703566311645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75003734687646419020328773 14063200253933703566311645)
                ·
                  refine ⟨5273700095225138837366867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14063200253933703566311645 5273700095225138837366867)
                  ·
                    refine ⟨7910550142837708256050301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273700095225138837366867 7910550142837708256050301)
                    ·
                      refine ⟨2966456303564140596018863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7910550142837708256050301 2966456303564140596018863)
                      ·
                        rfl

theorem cell23_5777153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_5777153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777153 prefixEnd_5777153 := by exact prefixLift 5777153
  have htrace : WordTrace (prefixWord ++ tailWord_5777153) baseStart_5777153 baseEnd_5777153 := by
    simpa [prefixWord, tailWord_5777153, baseEnd_5777153] using wordTrace_append hprefix tailTrace_5777153
  have hstable : (prefixWord ++ tailWord_5777153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777153).length < 2 ^ (prefixWord ++ tailWord_5777153).sum := by decide
  have hdescent : baseEnd_5777153 < baseStart_5777153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777163 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 2, 3, 2]
def baseStart_5777163 : Nat := 118140960795 + 5777163 * 2 ^ 59
def prefixEnd_5777163 : Nat := 4983230072969 + 3 ^ 40 * 5777163 * 2
def baseEnd_5777163 : Nat := 2966461438370685556893817

theorem tailTrace_5777163 : CollatzResearch.WordTrace tailWord_5777163 prefixEnd_5777163 2966461438370685556893817 := by
  unfold tailWord_5777163
  simp only [CollatzResearch.WordTrace]
  refine ⟨210710445169332586733424143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140473630112888391155616095 210710445169332586733424143)
  ·
    refine ⟨316065667753998880100136215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210710445169332586733424143 316065667753998880100136215)
    ·
      refine ⟨474098501630998320150204323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316065667753998880100136215 474098501630998320150204323)
      ·
        refine ⟨711147752446497480225306485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474098501630998320150204323 711147752446497480225306485)
        ·
          refine ⟨66670101791859138771122483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 711147752446497480225306485 66670101791859138771122483)
          ·
            refine ⟨100005152687788708156683725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66670101791859138771122483 100005152687788708156683725)
            ·
              refine ⟨37501932257920765558756397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100005152687788708156683725 37501932257920765558756397)
              ·
                refine ⟨14063224596720287084533649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37501932257920765558756397 14063224596720287084533649)
                ·
                  refine ⟨10547418447540215313400237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14063224596720287084533649 10547418447540215313400237)
                  ·
                    refine ⟨3955281917827580742525089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10547418447540215313400237 3955281917827580742525089)
                    ·
                      refine ⟨2966461438370685556893817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955281917827580742525089 2966461438370685556893817)
                      ·
                        rfl

theorem cell23_5777163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 3, 2].length) (baseStart_5777163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777163 prefixEnd_5777163 := by exact prefixLift 5777163
  have htrace : WordTrace (prefixWord ++ tailWord_5777163) baseStart_5777163 baseEnd_5777163 := by
    simpa [prefixWord, tailWord_5777163, baseEnd_5777163] using wordTrace_append hprefix tailTrace_5777163
  have hstable : (prefixWord ++ tailWord_5777163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777163).length < 2 ^ (prefixWord ++ tailWord_5777163).sum := by decide
  have hdescent : baseEnd_5777163 < baseStart_5777163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777186 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_5777186 : Nat := 118140960795 + 5777186 * 2 ^ 59
def prefixEnd_5777186 : Nat := 4983230072969 + 3 ^ 40 * 5777186 * 2
def baseEnd_5777186 : Nat := 988824416141912988968737

theorem tailTrace_5777186 : CollatzResearch.WordTrace tailWord_5777186 prefixEnd_5777186 988824416141912988968737 := by
  unfold tailWord_5777186
  simp only [CollatzResearch.WordTrace]
  refine ⟨52677821012062315415377853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140474189365499507774340941 52677821012062315415377853)
  ·
    refine ⟨19754182879523368280766695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52677821012062315415377853 19754182879523368280766695)
    ·
      refine ⟨29631274319285052421150043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19754182879523368280766695 29631274319285052421150043)
      ·
        refine ⟨44446911478927578631725065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29631274319285052421150043 44446911478927578631725065)
        ·
          refine ⟨33335183609195683973793799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44446911478927578631725065 33335183609195683973793799)
          ·
            refine ⟨50002775413793525960690699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33335183609195683973793799 50002775413793525960690699)
            ·
              refine ⟨75004163120690288941036049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50002775413793525960690699 75004163120690288941036049)
              ·
                refine ⟨56253122340517716705777037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75004163120690288941036049 56253122340517716705777037)
                ·
                  refine ⟨21094920877694143764666389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56253122340517716705777037 21094920877694143764666389)
                  ·
                    refine ⟨988824416141912988968737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21094920877694143764666389 988824416141912988968737)
                    ·
                      rfl

theorem cell23_5777186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_5777186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777186 prefixEnd_5777186 := by exact prefixLift 5777186
  have htrace : WordTrace (prefixWord ++ tailWord_5777186) baseStart_5777186 baseEnd_5777186 := by
    simpa [prefixWord, tailWord_5777186, baseEnd_5777186] using wordTrace_append hprefix tailTrace_5777186
  have hstable : (prefixWord ++ tailWord_5777186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777186).length < 2 ^ (prefixWord ++ tailWord_5777186).sum := by decide
  have hdescent : baseEnd_5777186 < baseStart_5777186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777187 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 1, 1, 3]
def baseStart_5777187 : Nat := 118140960795 + 5777187 * 2 ^ 59
def prefixEnd_5777187 : Nat := 4983230072969 + 3 ^ 40 * 5777187 * 2
def baseEnd_5777187 : Nat := 2966473761906393462993707

theorem tailTrace_5777187 : CollatzResearch.WordTrace tailWord_5777187 prefixEnd_5777187 2966473761906393462993707 := by
  unfold tailWord_5777187
  simp only [CollatzResearch.WordTrace]
  refine ⟨210711320521245638832297815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140474213680830425888198543 210711320521245638832297815)
  ·
    refine ⟨316066980781868458248446723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210711320521245638832297815 316066980781868458248446723)
    ·
      refine ⟨474100471172802687372670085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316066980781868458248446723 474100471172802687372670085)
      ·
        refine ⟨88893838344900503882375641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 474100471172802687372670085 88893838344900503882375641)
        ·
          refine ⟨66670378758675377911781731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88893838344900503882375641 66670378758675377911781731)
          ·
            refine ⟨100005568138013066867672597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66670378758675377911781731 100005568138013066867672597)
            ·
              refine ⟨4687761006469362509422153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100005568138013066867672597 4687761006469362509422153)
              ·
                refine ⟨3515820754852021882066615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687761006469362509422153 3515820754852021882066615)
                ·
                  refine ⟨5273731132278032823099923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515820754852021882066615 5273731132278032823099923)
                  ·
                    refine ⟨7910596698417049234649885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273731132278032823099923 7910596698417049234649885)
                    ·
                      refine ⟨2966473761906393462993707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7910596698417049234649885 2966473761906393462993707)
                      ·
                        rfl

theorem cell23_5777187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_5777187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777187 prefixEnd_5777187 := by exact prefixLift 5777187
  have htrace : WordTrace (prefixWord ++ tailWord_5777187) baseStart_5777187 baseEnd_5777187 := by
    simpa [prefixWord, tailWord_5777187, baseEnd_5777187] using wordTrace_append hprefix tailTrace_5777187
  have hstable : (prefixWord ++ tailWord_5777187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777187).length < 2 ^ (prefixWord ++ tailWord_5777187).sum := by decide
  have hdescent : baseEnd_5777187 < baseStart_5777187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777203 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 1, 6]
def baseStart_5777203 : Nat := 118140960795 + 5777203 * 2 ^ 59
def prefixEnd_5777203 : Nat := 4983230072969 + 3 ^ 40 * 5777203 * 2
def baseEnd_5777203 : Nat := 988827325865621800131211

theorem tailTrace_5777203 : CollatzResearch.WordTrace tailWord_5777203 prefixEnd_5777203 988827325865621800131211 := by
  unfold tailWord_5777203
  simp only [CollatzResearch.WordTrace]
  refine ⟨210711904089187673564880263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140474602726125115709920175 210711904089187673564880263)
  ·
    refine ⟨316067856133781510347320395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210711904089187673564880263 316067856133781510347320395)
    ·
      refine ⟨474101784200672265520980593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316067856133781510347320395 474101784200672265520980593)
      ·
        refine ⟨355576338150504199140735445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474101784200672265520980593 355576338150504199140735445)
        ·
          refine ⟨8333820425402442167360987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 355576338150504199140735445 8333820425402442167360987)
          ·
            refine ⟨12500730638103663251041481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333820425402442167360987 12500730638103663251041481)
            ·
              refine ⟨9375547978577747438281111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12500730638103663251041481 9375547978577747438281111)
              ·
                refine ⟨14063321967866621157421667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375547978577747438281111 14063321967866621157421667)
                ·
                  refine ⟨21094982951799931736132501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14063321967866621157421667 21094982951799931736132501)
                  ·
                    refine ⟨988827325865621800131211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21094982951799931736132501 988827325865621800131211)
                    ·
                      rfl

theorem cell23_5777203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 6].length) (baseStart_5777203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777203 prefixEnd_5777203 := by exact prefixLift 5777203
  have htrace : WordTrace (prefixWord ++ tailWord_5777203) baseStart_5777203 baseEnd_5777203 := by
    simpa [prefixWord, tailWord_5777203, baseEnd_5777203] using wordTrace_append hprefix tailTrace_5777203
  have hstable : (prefixWord ++ tailWord_5777203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777203).length < 2 ^ (prefixWord ++ tailWord_5777203).sum := by decide
  have hdescent : baseEnd_5777203 < baseStart_5777203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777210 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_5777210 : Nat := 118140960795 + 5777210 * 2 ^ 59
def prefixEnd_5777210 : Nat := 4983230072969 + 3 ^ 40 * 5777210 * 2
def baseEnd_5777210 : Nat := 2966485571961446873006101

theorem tailTrace_5777210 : CollatzResearch.WordTrace tailWord_5777210 prefixEnd_5777210 2966485571961446873006101 := by
  unfold tailWord_5777210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52678039850040578440096271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140474772933441542506923389 52678039850040578440096271)
  ·
    refine ⟨79017059775060867660144407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52678039850040578440096271 79017059775060867660144407)
    ·
      refine ⟨118525589662591301490216611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79017059775060867660144407 118525589662591301490216611)
      ·
        refine ⟨177788384493886952235324917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118525589662591301490216611 177788384493886952235324917)
        ·
          refine ⟨16667661046301901772061711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177788384493886952235324917 16667661046301901772061711)
          ·
            refine ⟨25001491569452852658092567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16667661046301901772061711 25001491569452852658092567)
            ·
              refine ⟨37502237354179278987138851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25001491569452852658092567 37502237354179278987138851)
              ·
                refine ⟨56253356031268918480708277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37502237354179278987138851 56253356031268918480708277)
                ·
                  refine ⟨5273752127931461107566401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56253356031268918480708277 5273752127931461107566401)
                  ·
                    refine ⟨3955314095948595830674801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273752127931461107566401 3955314095948595830674801)
                    ·
                      refine ⟨2966485571961446873006101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955314095948595830674801 2966485571961446873006101)
                      ·
                        rfl

theorem cell23_5777210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_5777210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777210 prefixEnd_5777210 := by exact prefixLift 5777210
  have htrace : WordTrace (prefixWord ++ tailWord_5777210) baseStart_5777210 baseEnd_5777210 := by
    simpa [prefixWord, tailWord_5777210, baseEnd_5777210] using wordTrace_append hprefix tailTrace_5777210
  have hstable : (prefixWord ++ tailWord_5777210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777210).length < 2 ^ (prefixWord ++ tailWord_5777210).sum := by decide
  have hdescent : baseEnd_5777210 < baseStart_5777210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777244 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5777244 : Nat := 118140960795 + 5777244 * 2 ^ 59
def prefixEnd_5777244 : Nat := 4983230072969 + 3 ^ 40 * 5777244 * 2
def baseEnd_5777244 : Nat := 2966503030303699739980945

theorem tailTrace_5777244 : CollatzResearch.WordTrace tailWord_5777244 prefixEnd_5777244 2966503030303699739980945 := by
  unfold tailWord_5777244
  simp only [CollatzResearch.WordTrace]
  refine ⟨105356699741019568783561393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140475599654692758378081857 105356699741019568783561393)
  ·
    refine ⟨79017524805764676587671045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105356699741019568783561393 79017524805764676587671045)
    ·
      refine ⟨14815785901080876860188321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79017524805764676587671045 14815785901080876860188321)
      ·
        refine ⟨11111839425810657645141241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14815785901080876860188321 11111839425810657645141241)
        ·
          refine ⟨8333879569357993233855931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11111839425810657645141241 8333879569357993233855931)
          ·
            refine ⟨12500819354036989850783897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333879569357993233855931 12500819354036989850783897)
            ·
              refine ⟨9375614515527742388087923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12500819354036989850783897 9375614515527742388087923)
              ·
                refine ⟨14063421773291613582131885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375614515527742388087923 14063421773291613582131885)
                ·
                  refine ⟨5273783164984355093299457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14063421773291613582131885 5273783164984355093299457)
                  ·
                    refine ⟨3955337373738266319974593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273783164984355093299457 3955337373738266319974593)
                    ·
                      refine ⟨2966503030303699739980945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955337373738266319974593 2966503030303699739980945)
                      ·
                        rfl

theorem cell23_5777244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5777244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777244 prefixEnd_5777244 := by exact prefixLift 5777244
  have htrace : WordTrace (prefixWord ++ tailWord_5777244) baseStart_5777244 baseEnd_5777244 := by
    simpa [prefixWord, tailWord_5777244, baseEnd_5777244] using wordTrace_append hprefix tailTrace_5777244
  have hstable : (prefixWord ++ tailWord_5777244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777244).length < 2 ^ (prefixWord ++ tailWord_5777244).sum := by decide
  have hdescent : baseEnd_5777244 < baseStart_5777244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777260 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_5777260 : Nat := 118140960795 + 5777260 * 2 ^ 59
def prefixEnd_5777260 : Nat := 4983230072969 + 3 ^ 40 * 5777260 * 2
def baseEnd_5777260 : Nat := 2966511245994171677380871

theorem tailTrace_5777260 : CollatzResearch.WordTrace tailWord_5777260 prefixEnd_5777260 2966511245994171677380871 := by
  unfold tailWord_5777260
  simp only [CollatzResearch.WordTrace]
  refine ⟨105356991524990586149852617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140475988699987448199803489 105356991524990586149852617)
  ·
    refine ⟨79017743643742939612389463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105356991524990586149852617 79017743643742939612389463)
    ·
      refine ⟨118526615465614409418584195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79017743643742939612389463 118526615465614409418584195)
      ·
        refine ⟨177789923198421614127876293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118526615465614409418584195 177789923198421614127876293)
        ·
          refine ⟨33335610599704052648976805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177789923198421614127876293 33335610599704052648976805)
          ·
            refine ⟨6250426987444509871683151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33335610599704052648976805 6250426987444509871683151)
            ·
              refine ⟨9375640481166764807524727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250426987444509871683151 9375640481166764807524727)
              ·
                refine ⟨14063460721750147211287091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9375640481166764807524727 14063460721750147211287091)
                ·
                  refine ⟨21095191082625220816930637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14063460721750147211287091 21095191082625220816930637)
                  ·
                    refine ⟨7910696655984457806348989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21095191082625220816930637 7910696655984457806348989)
                    ·
                      refine ⟨2966511245994171677380871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7910696655984457806348989 2966511245994171677380871)
                      ·
                        rfl

theorem cell23_5777260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_5777260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777260 prefixEnd_5777260 := by exact prefixLift 5777260
  have htrace : WordTrace (prefixWord ++ tailWord_5777260) baseStart_5777260 baseEnd_5777260 := by
    simpa [prefixWord, tailWord_5777260, baseEnd_5777260] using wordTrace_append hprefix tailTrace_5777260
  have hstable : (prefixWord ++ tailWord_5777260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777260).length < 2 ^ (prefixWord ++ tailWord_5777260).sum := by decide
  have hdescent : baseEnd_5777260 < baseStart_5777260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777278 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5777278 : Nat := 118140960795 + 5777278 * 2 ^ 59
def prefixEnd_5777278 : Nat := 4983230072969 + 3 ^ 40 * 5777278 * 2
def baseEnd_5777278 : Nat := 2966520488645952606955789

theorem tailTrace_5777278 : CollatzResearch.WordTrace tailWord_5777278 prefixEnd_5777278 2966520488645952606955789 := by
  unfold tailWord_5777278
  simp only [CollatzResearch.WordTrace]
  refine ⟨26339329945489495171732561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140476426375943974249240325 26339329945489495171732561)
  ·
    refine ⟨19754497459117121378799421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26339329945489495171732561 19754497459117121378799421)
    ·
      refine ⟨7407936547168920517049783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19754497459117121378799421 7407936547168920517049783)
      ·
        refine ⟨11111904820753380775574675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407936547168920517049783 11111904820753380775574675)
        ·
          refine ⟨16667857231130071163362013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11111904820753380775574675 16667857231130071163362013)
          ·
            refine ⟨6250446461673776686260755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16667857231130071163362013 6250446461673776686260755)
            ·
              refine ⟨9375669692510665029391133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250446461673776686260755 9375669692510665029391133)
              ·
                refine ⟨3515876134691499386021675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9375669692510665029391133 3515876134691499386021675)
                ·
                  refine ⟨5273814202037249079032513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3515876134691499386021675 5273814202037249079032513)
                  ·
                    refine ⟨3955360651527936809274385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5273814202037249079032513 3955360651527936809274385)
                    ·
                      refine ⟨2966520488645952606955789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955360651527936809274385 2966520488645952606955789)
                      ·
                        rfl

theorem cell23_5777278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5777278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777278 prefixEnd_5777278 := by exact prefixLift 5777278
  have htrace : WordTrace (prefixWord ++ tailWord_5777278) baseStart_5777278 baseEnd_5777278 := by
    simpa [prefixWord, tailWord_5777278, baseEnd_5777278] using wordTrace_append hprefix tailTrace_5777278
  have hstable : (prefixWord ++ tailWord_5777278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777278).length < 2 ^ (prefixWord ++ tailWord_5777278).sum := by decide
  have hdescent : baseEnd_5777278 < baseStart_5777278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777311 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 2, 1, 3]
def baseStart_5777311 : Nat := 118140960795 + 5777311 * 2 ^ 59
def prefixEnd_5777311 : Nat := 4983230072969 + 3 ^ 40 * 5777311 * 2
def baseEnd_5777311 : Nat := 2966537433507550977843137

theorem tailTrace_5777311 : CollatzResearch.WordTrace tailWord_5777311 prefixEnd_5777311 2966537433507550977843137 := by
  unfold tailWord_5777311
  simp only [CollatzResearch.WordTrace]
  refine ⟨210715843172796408009811787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140477228781864272006541191 210715843172796408009811787)
  ·
    refine ⟨316073764759194612014717681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210715843172796408009811787 316073764759194612014717681)
    ·
      refine ⟨237055323569395959011038261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316073764759194612014717681 237055323569395959011038261)
      ·
        refine ⟨22223936584630871157284837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237055323569395959011038261 22223936584630871157284837)
        ·
          refine ⟨4166988109618288341990907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22223936584630871157284837 4166988109618288341990907)
          ·
            refine ⟨6250482164427432512986361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166988109618288341990907 6250482164427432512986361)
            ·
              refine ⟨4687861623320574384739771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250482164427432512986361 4687861623320574384739771)
              ·
                refine ⟨7031792434980861577109657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4687861623320574384739771 7031792434980861577109657)
                ·
                  refine ⟨5273844326235646182832243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7031792434980861577109657 5273844326235646182832243)
                  ·
                    refine ⟨7910766489353469274248365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5273844326235646182832243 7910766489353469274248365)
                    ·
                      refine ⟨2966537433507550977843137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7910766489353469274248365 2966537433507550977843137)
                      ·
                        rfl

theorem cell23_5777311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_5777311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777311 prefixEnd_5777311 := by exact prefixLift 5777311
  have htrace : WordTrace (prefixWord ++ tailWord_5777311) baseStart_5777311 baseEnd_5777311 := by
    simpa [prefixWord, tailWord_5777311, baseEnd_5777311] using wordTrace_append hprefix tailTrace_5777311
  have hstable : (prefixWord ++ tailWord_5777311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777311).length < 2 ^ (prefixWord ++ tailWord_5777311).sum := by decide
  have hdescent : baseEnd_5777311 < baseStart_5777311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777390 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_5777390 : Nat := 118140960795 + 5777390 * 2 ^ 59
def prefixEnd_5777390 : Nat := 4983230072969 + 3 ^ 40 * 5777390 * 2
def baseEnd_5777390 : Nat := 2966577998479256168755273

theorem tailTrace_5777390 : CollatzResearch.WordTrace tailWord_5777390 prefixEnd_5777390 2966577998479256168755273 := by
  unfold tailWord_5777390
  simp only [CollatzResearch.WordTrace]
  refine ⟨26339840567438775562742203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140479149693006803001291749 26339840567438775562742203)
  ·
    refine ⟨39509760851158163344113305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26339840567438775562742203 39509760851158163344113305)
    ·
      refine ⟨29632320638368622508084979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39509760851158163344113305 29632320638368622508084979)
      ·
        refine ⟨44448480957552933762127469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29632320638368622508084979 44448480957552933762127469)
        ·
          refine ⟨16668180359082350160797801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44448480957552933762127469 16668180359082350160797801)
          ·
            refine ⟨12501135269311762620598351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16668180359082350160797801 12501135269311762620598351)
            ·
              refine ⟨18751702903967643930897527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12501135269311762620598351 18751702903967643930897527)
              ·
                refine ⟨28127554355951465896346291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18751702903967643930897527 28127554355951465896346291)
                ·
                  refine ⟨42191331533927198844519437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28127554355951465896346291 42191331533927198844519437)
                  ·
                    refine ⟨15821749325222699566694789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42191331533927198844519437 15821749325222699566694789)
                    ·
                      refine ⟨2966577998479256168755273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15821749325222699566694789 2966577998479256168755273)
                      ·
                        rfl

theorem cell23_5777390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_5777390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777390 prefixEnd_5777390 := by exact prefixLift 5777390
  have htrace : WordTrace (prefixWord ++ tailWord_5777390) baseStart_5777390 baseEnd_5777390 := by
    simpa [prefixWord, tailWord_5777390, baseEnd_5777390] using wordTrace_append hprefix tailTrace_5777390
  have hstable : (prefixWord ++ tailWord_5777390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777390).length < 2 ^ (prefixWord ++ tailWord_5777390).sum := by decide
  have hdescent : baseEnd_5777390 < baseStart_5777390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
