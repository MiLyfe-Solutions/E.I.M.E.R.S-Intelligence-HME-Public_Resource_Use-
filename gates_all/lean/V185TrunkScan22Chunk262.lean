import V185TrunkScan22Chunk261

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2337763 : List Nat := [1, 1, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_2337763 : Nat := 118140960795 + 2337763 * 2 ^ 59
def prefixEnd_2337763 : Nat := 4983230072969 + 3 ^ 40 * 2337763 * 2
def baseEnd_2337763 : Nat := 800264050197894816807553

theorem tailTrace_2337763 : CollatzResearch.WordTrace tailWord_2337763 prefixEnd_2337763 800264050197894816807553 := by
  unfold tailWord_2337763
  simp only [CollatzResearch.WordTrace]
  refine ⟨85265221429691383978945943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56843480953127589319297295 85265221429691383978945943)
  ·
    refine ⟨127897832144537075968418915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85265221429691383978945943 127897832144537075968418915)
    ·
      refine ⟨191846748216805613952628373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127897832144537075968418915 191846748216805613952628373)
      ·
        refine ⟨8992816322662763154029455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191846748216805613952628373 8992816322662763154029455)
        ·
          refine ⟨13489224483994144731044183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8992816322662763154029455 13489224483994144731044183)
          ·
            refine ⟨20233836725991217096566275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13489224483994144731044183 20233836725991217096566275)
            ·
              refine ⟨30350755088986825644849413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20233836725991217096566275 30350755088986825644849413)
              ·
                refine ⟨5690766579185029808409265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30350755088986825644849413 5690766579185029808409265)
                ·
                  refine ⟨4268074934388772356306949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5690766579185029808409265 4268074934388772356306949)
                  ·
                    refine ⟨800264050197894816807553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268074934388772356306949 800264050197894816807553)
                    ·
                      rfl

theorem cell22_2337763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_2337763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337763 prefixEnd_2337763 := by exact prefixLift 2337763
  have htrace : WordTrace (prefixWord ++ tailWord_2337763) baseStart_2337763 baseEnd_2337763 := by
    simpa [prefixWord, tailWord_2337763, baseEnd_2337763] using wordTrace_append hprefix tailTrace_2337763
  have hstable : (prefixWord ++ tailWord_2337763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337763).length < 2 ^ (prefixWord ++ tailWord_2337763).sum := by decide
  have hdescent : baseEnd_2337763 < baseStart_2337763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337767 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 4]
def baseStart_2337767 : Nat := 118140960795 + 2337767 * 2 ^ 59
def prefixEnd_2337767 : Nat := 4983230072969 + 3 ^ 40 * 2337767 * 2
def baseEnd_2337767 : Nat := 266755139826546713235847

theorem tailTrace_2337767 : CollatzResearch.WordTrace tailWord_2337767 prefixEnd_2337767 266755139826546713235847 := by
  unfold tailWord_2337767
  simp only [CollatzResearch.WordTrace]
  refine ⟨85265367321676892662091555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56843578214451261774727703 85265367321676892662091555)
  ·
    refine ⟨127898050982515338993137333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85265367321676892662091555 127898050982515338993137333)
    ·
      refine ⟨11990442279610813030606625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127898050982515338993137333 11990442279610813030606625)
      ·
        refine ⟨8992831709708109772954969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11990442279610813030606625 8992831709708109772954969)
        ·
          refine ⟨6744623782281082329716227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8992831709708109772954969 6744623782281082329716227)
          ·
            refine ⟨10116935673421623494574341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6744623782281082329716227 10116935673421623494574341)
            ·
              refine ⟨1896925438766554405232689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10116935673421623494574341 1896925438766554405232689)
              ·
                refine ⟨1422694079074915803924517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1896925438766554405232689 1422694079074915803924517)
                ·
                  refine ⟨266755139826546713235847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1422694079074915803924517 266755139826546713235847)
                  ·
                    rfl

theorem cell22_2337767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 4].length) (baseStart_2337767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337767 prefixEnd_2337767 := by exact prefixLift 2337767
  have htrace : WordTrace (prefixWord ++ tailWord_2337767) baseStart_2337767 baseEnd_2337767 := by
    simpa [prefixWord, tailWord_2337767, baseEnd_2337767] using wordTrace_append hprefix tailTrace_2337767
  have hstable : (prefixWord ++ tailWord_2337767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337767).length < 2 ^ (prefixWord ++ tailWord_2337767).sum := by decide
  have hdescent : baseEnd_2337767 < baseStart_2337767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_2337776 : Nat := 118140960795 + 2337776 * 2 ^ 59
def prefixEnd_2337776 : Nat := 4983230072969 + 3 ^ 40 * 2337776 * 2
def baseEnd_2337776 : Nat := 800268500363567116232513

theorem tailTrace_2337776 : CollatzResearch.WordTrace tailWord_2337776 prefixEnd_2337776 800268500363567116232513 := by
  unfold tailWord_2337776
  simp only [CollatzResearch.WordTrace]
  refine ⟨42632847789322143599584591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56843797052429524799446121 42632847789322143599584591)
  ·
    refine ⟨63949271683983215399376887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42632847789322143599584591 63949271683983215399376887)
    ·
      refine ⟨95923907525974823099065331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63949271683983215399376887 95923907525974823099065331)
      ·
        refine ⟨143885861288962234648597997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95923907525974823099065331 143885861288962234648597997)
        ·
          refine ⟨53957197983360837993224249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143885861288962234648597997 53957197983360837993224249)
          ·
            refine ⟨40467898487520628494918187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53957197983360837993224249 40467898487520628494918187)
            ·
              refine ⟨60701847731280942742377281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40467898487520628494918187 60701847731280942742377281)
              ·
                refine ⟨45526385798460707056782961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60701847731280942742377281 45526385798460707056782961)
                ·
                  refine ⟨34144789348845530292587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45526385798460707056782961 34144789348845530292587221)
                  ·
                    refine ⟨800268500363567116232513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34144789348845530292587221 800268500363567116232513)
                    ·
                      rfl

theorem cell22_2337776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_2337776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337776 prefixEnd_2337776 := by exact prefixLift 2337776
  have htrace : WordTrace (prefixWord ++ tailWord_2337776) baseStart_2337776 baseEnd_2337776 := by
    simpa [prefixWord, tailWord_2337776, baseEnd_2337776] using wordTrace_append hprefix tailTrace_2337776
  have hstable : (prefixWord ++ tailWord_2337776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337776).length < 2 ^ (prefixWord ++ tailWord_2337776).sum := by decide
  have hdescent : baseEnd_2337776 < baseStart_2337776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337782 : List Nat := [5, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_2337782 : Nat := 118140960795 + 2337782 * 2 ^ 59
def prefixEnd_2337782 : Nat := 4983230072969 + 3 ^ 40 * 2337782 * 2
def baseEnd_2337782 : Nat := 800270554286185100582495

theorem tailTrace_2337782 : CollatzResearch.WordTrace tailWord_2337782 prefixEnd_2337782 800270554286185100582495 := by
  unfold tailWord_2337782
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329119651038909388992975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56843942944415033482591733 5329119651038909388992975)
  ·
    refine ⟨7993679476558364083489463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5329119651038909388992975 7993679476558364083489463)
    ·
      refine ⟨11990519214837546125234195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7993679476558364083489463 11990519214837546125234195)
      ·
        refine ⟨17985778822256319187851293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11990519214837546125234195 17985778822256319187851293)
        ·
          refine ⟨6744667058346119695444235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17985778822256319187851293 6744667058346119695444235)
          ·
            refine ⟨10117000587519179543166353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6744667058346119695444235 10117000587519179543166353)
            ·
              refine ⟨7587750440639384657374765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10117000587519179543166353 7587750440639384657374765)
              ·
                refine ⟨2845406415239769246515537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7587750440639384657374765 2845406415239769246515537)
                ·
                  refine ⟨2134054811429826934886653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845406415239769246515537 2134054811429826934886653)
                  ·
                    refine ⟨800270554286185100582495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134054811429826934886653 800270554286185100582495)
                    ·
                      rfl

theorem cell22_2337782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_2337782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337782 prefixEnd_2337782 := by exact prefixLift 2337782
  have htrace : WordTrace (prefixWord ++ tailWord_2337782) baseStart_2337782 baseEnd_2337782 := by
    simpa [prefixWord, tailWord_2337782, baseEnd_2337782] using wordTrace_append hprefix tailTrace_2337782
  have hstable : (prefixWord ++ tailWord_2337782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337782).length < 2 ^ (prefixWord ++ tailWord_2337782).sum := by decide
  have hdescent : baseEnd_2337782 < baseStart_2337782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337823 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 7]
def baseStart_2337823 : Nat := 118140960795 + 2337823 * 2 ^ 59
def prefixEnd_2337823 : Nat := 4983230072969 + 3 ^ 40 * 2337823 * 2
def baseEnd_2337823 : Nat := 266761529808024886769123

theorem tailTrace_2337823 : CollatzResearch.WordTrace tailWord_2337823 prefixEnd_2337823 266761529808024886769123 := by
  unfold tailWord_2337823
  simp only [CollatzResearch.WordTrace]
  refine ⟨85267409809474014226130123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56844939872982676150753415 85267409809474014226130123)
  ·
    refine ⟨127901114714211021339195185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85267409809474014226130123 127901114714211021339195185)
    ·
      refine ⟨95925836035658266004396389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127901114714211021339195185 95925836035658266004396389)
      ·
        refine ⟨17986094256685924875824323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95925836035658266004396389 17986094256685924875824323)
        ·
          refine ⟨26979141385028887313736485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17986094256685924875824323 26979141385028887313736485)
          ·
            refine ⟨5058589009692916371325591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26979141385028887313736485 5058589009692916371325591)
            ·
              refine ⟨7587883514539374556988387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5058589009692916371325591 7587883514539374556988387)
              ·
                refine ⟨11381825271809061835482581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7587883514539374556988387 11381825271809061835482581)
                ·
                  refine ⟨266761529808024886769123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11381825271809061835482581 266761529808024886769123)
                  ·
                    rfl

theorem cell22_2337823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_2337823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337823 prefixEnd_2337823 := by exact prefixLift 2337823
  have htrace : WordTrace (prefixWord ++ tailWord_2337823) baseStart_2337823 baseEnd_2337823 := by
    simpa [prefixWord, tailWord_2337823, baseEnd_2337823] using wordTrace_append hprefix tailTrace_2337823
  have hstable : (prefixWord ++ tailWord_2337823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337823).length < 2 ^ (prefixWord ++ tailWord_2337823).sum := by decide
  have hdescent : baseEnd_2337823 < baseStart_2337823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337827 : List Nat := [1, 1, 1, 4, 3, 2, 2, 4, 1, 3]
def baseStart_2337827 : Nat := 118140960795 + 2337827 * 2 ^ 59
def prefixEnd_2337827 : Nat := 4983230072969 + 3 ^ 40 * 2337827 * 2
def baseEnd_2337827 : Nat := 800285958705819983207357

theorem tailTrace_2337827 : CollatzResearch.WordTrace tailWord_2337827 prefixEnd_2337827 800285958705819983207357 := by
  unfold tailWord_2337827
  simp only [CollatzResearch.WordTrace]
  refine ⟨85267555701459522909275735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56845037134306348606183823 85267555701459522909275735)
  ·
    refine ⟨127901333552189284363913603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85267555701459522909275735 127901333552189284363913603)
    ·
      refine ⟨191852000328283926545870405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127901333552189284363913603 191852000328283926545870405)
      ·
        refine ⟨35972250061553236227350701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191852000328283926545870405 35972250061553236227350701)
        ·
          refine ⟨13489593773082463585256513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35972250061553236227350701 13489593773082463585256513)
          ·
            refine ⟨10117195329811847688942385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13489593773082463585256513 10117195329811847688942385)
            ·
              refine ⟨7587896497358885766706789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10117195329811847688942385 7587896497358885766706789)
              ·
                refine ⟨1422730593254791081257523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7587896497358885766706789 1422730593254791081257523)
                ·
                  refine ⟨2134095889882186621886285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1422730593254791081257523 2134095889882186621886285)
                  ·
                    refine ⟨800285958705819983207357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134095889882186621886285 800285958705819983207357)
                    ·
                      rfl

theorem cell22_2337827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 3].length) (baseStart_2337827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337827 prefixEnd_2337827 := by exact prefixLift 2337827
  have htrace : WordTrace (prefixWord ++ tailWord_2337827) baseStart_2337827 baseEnd_2337827 := by
    simpa [prefixWord, tailWord_2337827, baseEnd_2337827] using wordTrace_append hprefix tailTrace_2337827
  have hstable : (prefixWord ++ tailWord_2337827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337827).length < 2 ^ (prefixWord ++ tailWord_2337827).sum := by decide
  have hdescent : baseEnd_2337827 < baseStart_2337827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337840 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_2337840 : Nat := 118140960795 + 2337840 * 2 ^ 59
def prefixEnd_2337840 : Nat := 4983230072969 + 3 ^ 40 * 2337840 * 2
def baseEnd_2337840 : Nat := 266763469623830760877439

theorem tailTrace_2337840 : CollatzResearch.WordTrace tailWord_2337840 prefixEnd_2337840 266763469623830760877439 := by
  unfold tailWord_2337840
  simp only [CollatzResearch.WordTrace]
  refine ⟨42634014925206213064749487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56845353233608284086332649 42634014925206213064749487)
  ·
    refine ⟨63951022387809319597124231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42634014925206213064749487 63951022387809319597124231)
    ·
      refine ⟨95926533581713979395686347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63951022387809319597124231 95926533581713979395686347)
      ·
        refine ⟨143889800372570969093529521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95926533581713979395686347 143889800372570969093529521)
        ·
          refine ⟨107917350279428226820147141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143889800372570969093529521 107917350279428226820147141)
          ·
            refine ⟨20234503177392792528777589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107917350279428226820147141 20234503177392792528777589)
            ·
              refine ⟨1896984672880574299572899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20234503177392792528777589 1896984672880574299572899)
              ·
                refine ⟨2845477009320861449359349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1896984672880574299572899 2845477009320861449359349)
                ·
                  refine ⟨266763469623830760877439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845477009320861449359349 266763469623830760877439)
                  ·
                    rfl

theorem cell22_2337840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_2337840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337840 prefixEnd_2337840 := by exact prefixLift 2337840
  have htrace : WordTrace (prefixWord ++ tailWord_2337840) baseStart_2337840 baseEnd_2337840 := by
    simpa [prefixWord, tailWord_2337840, baseEnd_2337840] using wordTrace_append hprefix tailTrace_2337840
  have hstable : (prefixWord ++ tailWord_2337840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337840).length < 2 ^ (prefixWord ++ tailWord_2337840).sum := by decide
  have hdescent : baseEnd_2337840 < baseStart_2337840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337870 : List Nat := [4, 1, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_2337870 : Nat := 118140960795 + 2337870 * 2 ^ 59
def prefixEnd_2337870 : Nat := 4983230072969 + 3 ^ 40 * 2337870 * 2
def baseEnd_2337870 : Nat := 800300678484582204382225

theorem tailTrace_2337870 : CollatzResearch.WordTrace tailWord_2337870 prefixEnd_2337870 800300678484582204382225 := by
  unfold tailWord_2337870
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658640505037967656636383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56846082693535827502060709 10658640505037967656636383)
  ·
    refine ⟨15987960757556951484954575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10658640505037967656636383 15987960757556951484954575)
    ·
      refine ⟨23981941136335427227431863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15987960757556951484954575 23981941136335427227431863)
      ·
        refine ⟨35972911704503140841147795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23981941136335427227431863 35972911704503140841147795)
        ·
          refine ⟨53959367556754711261721693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35972911704503140841147795 53959367556754711261721693)
          ·
            refine ⟨20234762833783016723145635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53959367556754711261721693 20234762833783016723145635)
            ·
              refine ⟨30352144250674525084718453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20234762833783016723145635 30352144250674525084718453)
              ·
                refine ⟨2845513523500736726692355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30352144250674525084718453 2845513523500736726692355)
                ·
                  refine ⟨4268270285251105090038533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2845513523500736726692355 4268270285251105090038533)
                  ·
                    refine ⟨800300678484582204382225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4268270285251105090038533 800300678484582204382225)
                    ·
                      rfl

theorem cell22_2337870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_2337870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337870 prefixEnd_2337870 := by exact prefixLift 2337870
  have htrace : WordTrace (prefixWord ++ tailWord_2337870) baseStart_2337870 baseEnd_2337870 := by
    simpa [prefixWord, tailWord_2337870, baseEnd_2337870] using wordTrace_append hprefix tailTrace_2337870
  have hstable : (prefixWord ++ tailWord_2337870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337870).length < 2 ^ (prefixWord ++ tailWord_2337870).sum := by decide
  have hdescent : baseEnd_2337870 < baseStart_2337870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337878 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2337878 : Nat := 118140960795 + 2337878 * 2 ^ 59
def prefixEnd_2337878 : Nat := 4983230072969 + 3 ^ 40 * 2337878 * 2
def baseEnd_2337878 : Nat := 800303417048072850182201

theorem tailTrace_2337878 : CollatzResearch.WordTrace tailWord_2337878 prefixEnd_2337878 800303417048072850182201 := by
  unfold tailWord_2337878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5329338489017172413711393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56846277216183172412921525 5329338489017172413711393)
  ·
    refine ⟨3997003866762879310283545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5329338489017172413711393 3997003866762879310283545)
    ·
      refine ⟨2997752900072159482712659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3997003866762879310283545 2997752900072159482712659)
      ·
        refine ⟨4496629350108239224068989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997752900072159482712659 4496629350108239224068989)
        ·
          refine ⟨1686236006290589709025871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4496629350108239224068989 1686236006290589709025871)
          ·
            refine ⟨2529354009435884563538807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686236006290589709025871 2529354009435884563538807)
            ·
              refine ⟨3794031014153826845308211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529354009435884563538807 3794031014153826845308211)
              ·
                refine ⟨5691046521230740267962317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794031014153826845308211 5691046521230740267962317)
                ·
                  refine ⟨2134142445461527600485869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5691046521230740267962317 2134142445461527600485869)
                  ·
                    refine ⟨800303417048072850182201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134142445461527600485869 800303417048072850182201)
                    ·
                      rfl

theorem cell22_2337878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2337878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337878 prefixEnd_2337878 := by exact prefixLift 2337878
  have htrace : WordTrace (prefixWord ++ tailWord_2337878) baseStart_2337878 baseEnd_2337878 := by
    simpa [prefixWord, tailWord_2337878, baseEnd_2337878] using wordTrace_append hprefix tailTrace_2337878
  have hstable : (prefixWord ++ tailWord_2337878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337878).length < 2 ^ (prefixWord ++ tailWord_2337878).sum := by decide
  have hdescent : baseEnd_2337878 < baseStart_2337878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2337934 : List Nat := [4, 1, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_2337934 : Nat := 118140960795 + 2337934 * 2 ^ 59
def prefixEnd_2337934 : Nat := 4983230072969 + 3 ^ 40 * 2337934 * 2
def baseEnd_2337934 : Nat := 800322586992507370782029

theorem tailTrace_2337934 : CollatzResearch.WordTrace tailWord_2337934 prefixEnd_2337934 800322586992507370782029 := by
  unfold tailWord_2337934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10658932289008985022927607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56847638874714586788947237 10658932289008985022927607)
  ·
    refine ⟨15988398433513477534391411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10658932289008985022927607 15988398433513477534391411)
    ·
      refine ⟨23982597650270216301587117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15988398433513477534391411 23982597650270216301587117)
      ·
        refine ⟨8993474118851331113095169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23982597650270216301587117 8993474118851331113095169)
        ·
          refine ⟨6745105589138498334821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8993474118851331113095169 6745105589138498334821377)
          ·
            refine ⟨5058829191853873751116033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6745105589138498334821377 5058829191853873751116033)
            ·
              refine ⟨3794121893890405313337025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5058829191853873751116033 3794121893890405313337025)
              ·
                refine ⟨2845591420417803985002769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3794121893890405313337025 2845591420417803985002769)
                ·
                  refine ⟨2134193565313352988752077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2845591420417803985002769 2134193565313352988752077)
                  ·
                    refine ⟨800322586992507370782029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134193565313352988752077 800322586992507370782029)
                    ·
                      rfl

theorem cell22_2337934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_2337934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2337934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2337934 prefixEnd_2337934 := by exact prefixLift 2337934
  have htrace : WordTrace (prefixWord ++ tailWord_2337934) baseStart_2337934 baseEnd_2337934 := by
    simpa [prefixWord, tailWord_2337934, baseEnd_2337934] using wordTrace_append hprefix tailTrace_2337934
  have hstable : (prefixWord ++ tailWord_2337934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2337934).length < 2 ^ (prefixWord ++ tailWord_2337934).sum := by decide
  have hdescent : baseEnd_2337934 < baseStart_2337934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2337934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338003 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 10]
def baseStart_2338003 : Nat := 118140960795 + 2338003 * 2 ^ 59
def prefixEnd_2338003 : Nat := 4983230072969 + 3 ^ 40 * 2338003 * 2
def baseEnd_2338003 : Nat := 266782069034204730268939

theorem tailTrace_2338003 : CollatzResearch.WordTrace tailWord_2338003 prefixEnd_2338003 266782069034204730268939 := by
  unfold tailWord_2338003
  simp only [CollatzResearch.WordTrace]
  refine ⟨85273974948821904967682663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56849316632547936645121775 85273974948821904967682663)
  ·
    refine ⟨127910962423232857451523995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85273974948821904967682663 127910962423232857451523995)
    ·
      refine ⟨191866443634849286177285993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127910962423232857451523995 191866443634849286177285993)
      ·
        refine ⟨143899832726136964632964495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191866443634849286177285993 143899832726136964632964495)
        ·
          refine ⟨215849749089205446949446743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143899832726136964632964495 215849749089205446949446743)
          ·
            refine ⟨323774623633808170424170115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215849749089205446949446743 323774623633808170424170115)
            ·
              refine ⟨485661935450712255636255173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323774623633808170424170115 485661935450712255636255173)
              ·
                refine ⟨91061612897008547931797845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485661935450712255636255173 91061612897008547931797845)
                ·
                  refine ⟨266782069034204730268939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91061612897008547931797845 266782069034204730268939)
                  ·
                    rfl

theorem cell22_2338003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_2338003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338003 prefixEnd_2338003 := by exact prefixLift 2338003
  have htrace : WordTrace (prefixWord ++ tailWord_2338003) baseStart_2338003 baseEnd_2338003 := by
    simpa [prefixWord, tailWord_2338003, baseEnd_2338003] using wordTrace_append hprefix tailTrace_2338003
  have hstable : (prefixWord ++ tailWord_2338003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338003).length < 2 ^ (prefixWord ++ tailWord_2338003).sum := by decide
  have hdescent : baseEnd_2338003 < baseStart_2338003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338020 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_2338020 : Nat := 118140960795 + 2338020 * 2 ^ 59
def prefixEnd_2338020 : Nat := 4983230072969 + 3 ^ 40 * 2338020 * 2
def baseEnd_2338020 : Nat := 266784008850010604377255

theorem tailTrace_2338020 : CollatzResearch.WordTrace tailWord_2338020 prefixEnd_2338020 266784008850010604377255 := by
  unfold tailWord_2338020
  simp only [CollatzResearch.WordTrace]
  refine ⟨42637297494880158435525757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56849729993173544580701009 42637297494880158435525757)
  ·
    refine ⟨15988986560580059413322159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42637297494880158435525757 15988986560580059413322159)
    ·
      refine ⟨23983479840870089119983239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15988986560580059413322159 23983479840870089119983239)
      ·
        refine ⟨35975219761305133679974859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23983479840870089119983239 35975219761305133679974859)
        ·
          refine ⟨53962829641957700519962289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35975219761305133679974859 53962829641957700519962289)
          ·
            refine ⟨40472122231468275389971717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53962829641957700519962289 40472122231468275389971717)
            ·
              refine ⟨7588522918400301635619697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40472122231468275389971717 7588522918400301635619697)
              ·
                refine ⟨5691392188800226226714773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7588522918400301635619697 5691392188800226226714773)
                ·
                  refine ⟨266784008850010604377255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5691392188800226226714773 266784008850010604377255)
                  ·
                    rfl

theorem cell22_2338020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_2338020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338020 prefixEnd_2338020 := by exact prefixLift 2338020
  have htrace : WordTrace (prefixWord ++ tailWord_2338020) baseStart_2338020 baseEnd_2338020 := by
    simpa [prefixWord, tailWord_2338020, baseEnd_2338020] using wordTrace_append hprefix tailTrace_2338020
  have hstable : (prefixWord ++ tailWord_2338020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338020).length < 2 ^ (prefixWord ++ tailWord_2338020).sum := by decide
  have hdescent : baseEnd_2338020 < baseStart_2338020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338065 : List Nat := [1, 2, 2, 1, 1, 4, 4, 7]
def baseStart_2338065 : Nat := 118140960795 + 2338065 * 2 ^ 59
def prefixEnd_2338065 : Nat := 4983230072969 + 3 ^ 40 * 2338065 * 2
def baseEnd_2338065 : Nat := 88929714552185188417403

theorem tailTrace_2338065 : CollatzResearch.WordTrace tailWord_2338065 prefixEnd_2338065 88929714552185188417403 := by
  unfold tailWord_2338065
  simp only [CollatzResearch.WordTrace]
  refine ⟨85276236274597289556439649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56850824183064859704293099 85276236274597289556439649)
  ·
    refine ⟨63957177205947967167329737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85276236274597289556439649 63957177205947967167329737)
    ·
      refine ⟨47967882904460975375497303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63957177205947967167329737 47967882904460975375497303)
      ·
        refine ⟨71951824356691463063245955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47967882904460975375497303 71951824356691463063245955)
        ·
          refine ⟨107927736535037194594868933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71951824356691463063245955 107927736535037194594868933)
          ·
            refine ⟨20236450600319473986537925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107927736535037194594868933 20236450600319473986537925)
            ·
              refine ⟨3794334487559901372475861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20236450600319473986537925 3794334487559901372475861)
              ·
                refine ⟨88929714552185188417403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3794334487559901372475861 88929714552185188417403)
                ·
                  rfl

theorem cell22_2338065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 7].length) (baseStart_2338065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338065 prefixEnd_2338065 := by exact prefixLift 2338065
  have htrace : WordTrace (prefixWord ++ tailWord_2338065) baseStart_2338065 baseEnd_2338065 := by
    simpa [prefixWord, tailWord_2338065, baseEnd_2338065] using wordTrace_append hprefix tailTrace_2338065
  have hstable : (prefixWord ++ tailWord_2338065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338065).length < 2 ^ (prefixWord ++ tailWord_2338065).sum := by decide
  have hdescent : baseEnd_2338065 < baseStart_2338065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338172 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_2338172 : Nat := 118140960795 + 2338172 * 2 ^ 59
def prefixEnd_2338172 : Nat := 4983230072969 + 3 ^ 40 * 2338172 * 2
def baseEnd_2338172 : Nat := 266801353085451361110433

theorem tailTrace_2338172 : CollatzResearch.WordTrace tailWord_2338172 prefixEnd_2338172 266801353085451361110433 := by
  unfold tailWord_2338172
  simp only [CollatzResearch.WordTrace]
  refine ⟨42640069442604823415292385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56853425923473097887056513 42640069442604823415292385)
  ·
    refine ⟨31980052081953617561469289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42640069442604823415292385 31980052081953617561469289)
    ·
      refine ⟨23985039061465213171101967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31980052081953617561469289 23985039061465213171101967)
      ·
        refine ⟨35977558592197819756652951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23985039061465213171101967 35977558592197819756652951)
        ·
          refine ⟨53966337888296729634979427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35977558592197819756652951 53966337888296729634979427)
          ·
            refine ⟨80949506832445094452469141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53966337888296729634979427 80949506832445094452469141)
            ·
              refine ⟨3794508132770863802459491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80949506832445094452469141 3794508132770863802459491)
              ·
                refine ⟨5691762199156295703689237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3794508132770863802459491 5691762199156295703689237)
                ·
                  refine ⟨266801353085451361110433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5691762199156295703689237 266801353085451361110433)
                  ·
                    rfl

theorem cell22_2338172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_2338172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338172 prefixEnd_2338172 := by exact prefixLift 2338172
  have htrace : WordTrace (prefixWord ++ tailWord_2338172) baseStart_2338172 baseEnd_2338172 := by
    simpa [prefixWord, tailWord_2338172, baseEnd_2338172] using wordTrace_append hprefix tailTrace_2338172
  have hstable : (prefixWord ++ tailWord_2338172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338172).length < 2 ^ (prefixWord ++ tailWord_2338172).sum := by decide
  have hdescent : baseEnd_2338172 < baseStart_2338172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338178 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2338178 : Nat := 118140960795 + 2338178 * 2 ^ 59
def prefixEnd_2338178 : Nat := 4983230072969 + 3 ^ 40 * 2338178 * 2
def baseEnd_2338178 : Nat := 266802037726324022560427

theorem tailTrace_2338178 : CollatzResearch.WordTrace tailWord_2338178 prefixEnd_2338178 266802037726324022560427 := by
  unfold tailWord_2338178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320089430796977463825797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56853571815458606570202125 21320089430796977463825797)
  ·
    refine ⟨3997516768274433274467337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21320089430796977463825797 3997516768274433274467337)
    ·
      refine ⟨2998137576205824955850503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3997516768274433274467337 2998137576205824955850503)
      ·
        refine ⟨4497206364308737433775755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2998137576205824955850503 4497206364308737433775755)
        ·
          refine ⟨6745809546463106150663633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497206364308737433775755 6745809546463106150663633)
          ·
            refine ⟨5059357159847329612997725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6745809546463106150663633 5059357159847329612997725)
            ·
              refine ⟨1897258934942748604874147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5059357159847329612997725 1897258934942748604874147)
              ·
                refine ⟨2845888402414122907311221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1897258934942748604874147 2845888402414122907311221)
                ·
                  refine ⟨266802037726324022560427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2845888402414122907311221 266802037726324022560427)
                  ·
                    rfl

theorem cell22_2338178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2338178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338178 prefixEnd_2338178 := by exact prefixLift 2338178
  have htrace : WordTrace (prefixWord ++ tailWord_2338178) baseStart_2338178 baseEnd_2338178 := by
    simpa [prefixWord, tailWord_2338178, baseEnd_2338178] using wordTrace_append hprefix tailTrace_2338178
  have hstable : (prefixWord ++ tailWord_2338178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338178).length < 2 ^ (prefixWord ++ tailWord_2338178).sum := by decide
  have hdescent : baseEnd_2338178 < baseStart_2338178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338202 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_2338202 : Nat := 118140960795 + 2338202 * 2 ^ 59
def prefixEnd_2338202 : Nat := 4983230072969 + 3 ^ 40 * 2338202 * 2
def baseEnd_2338202 : Nat := 800414328869444005081207

theorem tailTrace_2338202 : CollatzResearch.WordTrace tailWord_2338202 prefixEnd_2338202 800414328869444005081207 := by
  unfold tailWord_2338202
  simp only [CollatzResearch.WordTrace]
  refine ⟨21320308268775240488544215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56854155383400641302784573 21320308268775240488544215)
  ·
    refine ⟨31980462403162860732816323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21320308268775240488544215 31980462403162860732816323)
    ·
      refine ⟨47970693604744291099224485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31980462403162860732816323 47970693604744291099224485)
      ·
        refine ⟨8994505050889554581104591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47970693604744291099224485 8994505050889554581104591)
        ·
          refine ⟨13491757576334331871656887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994505050889554581104591 13491757576334331871656887)
          ·
            refine ⟨20237636364501497807485331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13491757576334331871656887 20237636364501497807485331)
            ·
              refine ⟨30356454546752246711227997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20237636364501497807485331 30356454546752246711227997)
              ·
                refine ⟨11383670455032092516710499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30356454546752246711227997 11383670455032092516710499)
                ·
                  refine ⟨17075505682548138775065749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11383670455032092516710499 17075505682548138775065749)
                  ·
                    refine ⟨800414328869444005081207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17075505682548138775065749 800414328869444005081207)
                    ·
                      rfl

theorem cell22_2338202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_2338202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338202 prefixEnd_2338202 := by exact prefixLift 2338202
  have htrace : WordTrace (prefixWord ++ tailWord_2338202) baseStart_2338202 baseEnd_2338202 := by
    simpa [prefixWord, tailWord_2338202, baseEnd_2338202] using wordTrace_append hprefix tailTrace_2338202
  have hstable : (prefixWord ++ tailWord_2338202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338202).length < 2 ^ (prefixWord ++ tailWord_2338202).sum := by decide
  have hdescent : baseEnd_2338202 < baseStart_2338202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338221 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 4, 3]
def baseStart_2338221 : Nat := 118140960795 + 2338221 * 2 ^ 59
def prefixEnd_2338221 : Nat := 4983230072969 + 3 ^ 40 * 2338221 * 2
def baseEnd_2338221 : Nat := 800420832957734288856149

theorem tailTrace_2338221 : CollatzResearch.WordTrace tailWord_2338221 prefixEnd_2338221 800420832957734288856149 := by
  unfold tailWord_2338221
  simp only [CollatzResearch.WordTrace]
  refine ⟨85281926062032128199118517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56854617374688085466079011 85281926062032128199118517)
  ·
    refine ⟨7995180568315512018667361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85281926062032128199118517 7995180568315512018667361)
    ·
      refine ⟨5996385426236634014000521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7995180568315512018667361 5996385426236634014000521)
      ·
        refine ⟨4497289069677475510500391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5996385426236634014000521 4497289069677475510500391)
        ·
          refine ⟨6745933604516213265750587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4497289069677475510500391 6745933604516213265750587)
          ·
            refine ⟨10118900406774319898625881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6745933604516213265750587 10118900406774319898625881)
            ·
              refine ⟨7589175305080739923969411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10118900406774319898625881 7589175305080739923969411)
              ·
                refine ⟨11383762957621109885954117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589175305080739923969411 11383762957621109885954117)
                ·
                  refine ⟨2134455554553958103616397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11383762957621109885954117 2134455554553958103616397)
                  ·
                    refine ⟨800420832957734288856149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134455554553958103616397 800420832957734288856149)
                    ·
                      rfl

theorem cell22_2338221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_2338221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338221 prefixEnd_2338221 := by exact prefixLift 2338221
  have htrace : WordTrace (prefixWord ++ tailWord_2338221) baseStart_2338221 baseEnd_2338221 := by
    simpa [prefixWord, tailWord_2338221, baseEnd_2338221] using wordTrace_append hprefix tailTrace_2338221
  have hstable : (prefixWord ++ tailWord_2338221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338221).length < 2 ^ (prefixWord ++ tailWord_2338221).sum := by decide
  have hdescent : baseEnd_2338221 < baseStart_2338221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338279 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 5]
def baseStart_2338279 : Nat := 118140960795 + 2338279 * 2 ^ 59
def prefixEnd_2338279 : Nat := 4983230072969 + 3 ^ 40 * 2338279 * 2
def baseEnd_2338279 : Nat := 266813562514347156968657

theorem tailTrace_2338279 : CollatzResearch.WordTrace tailWord_2338279 prefixEnd_2338279 266813562514347156968657 := by
  unfold tailWord_2338279
  simp only [CollatzResearch.WordTrace]
  refine ⟨85284041495822004104729891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56856027663881336069819927 85284041495822004104729891)
  ·
    refine ⟨127926062243733006157094837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85284041495822004104729891 127926062243733006157094837)
    ·
      refine ⟨11993068335349969327227641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127926062243733006157094837 11993068335349969327227641)
      ·
        refine ⟨8994801251512476995420731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11993068335349969327227641 8994801251512476995420731)
        ·
          refine ⟨13492201877268715493131097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8994801251512476995420731 13492201877268715493131097)
          ·
            refine ⟨10119151407951536619848323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13492201877268715493131097 10119151407951536619848323)
            ·
              refine ⟨15178727111927304929772485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10119151407951536619848323 15178727111927304929772485)
              ·
                refine ⟨2846011333486369674332341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15178727111927304929772485 2846011333486369674332341)
                ·
                  refine ⟨266813562514347156968657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2846011333486369674332341 266813562514347156968657)
                  ·
                    rfl

theorem cell22_2338279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 5].length) (baseStart_2338279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338279 prefixEnd_2338279 := by exact prefixLift 2338279
  have htrace : WordTrace (prefixWord ++ tailWord_2338279) baseStart_2338279 baseEnd_2338279 := by
    simpa [prefixWord, tailWord_2338279, baseEnd_2338279] using wordTrace_append hprefix tailTrace_2338279
  have hstable : (prefixWord ++ tailWord_2338279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338279).length < 2 ^ (prefixWord ++ tailWord_2338279).sum := by decide
  have hdescent : baseEnd_2338279 < baseStart_2338279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338294 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2338294 : Nat := 118140960795 + 2338294 * 2 ^ 59
def prefixEnd_2338294 : Nat := 4983230072969 + 3 ^ 40 * 2338294 * 2
def baseEnd_2338294 : Nat := 800445822349586431780925

theorem tailTrace_2338294 : CollatzResearch.WordTrace tailWord_2338294 prefixEnd_2338294 800445822349586431780925 := by
  unfold tailWord_2338294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330286786922978854157871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56856392393845107777683957 5330286786922978854157871)
  ·
    refine ⟨7995430180384468281236807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5330286786922978854157871 7995430180384468281236807)
    ·
      refine ⟨11993145270576702421855211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7995430180384468281236807 11993145270576702421855211)
      ·
        refine ⟨17989717905865053632782817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11993145270576702421855211 17989717905865053632782817)
        ·
          refine ⟨13492288429398790224587113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17989717905865053632782817 13492288429398790224587113)
          ·
            refine ⟨10119216322049092668440335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13492288429398790224587113 10119216322049092668440335)
            ·
              refine ⟨15178824483073639002660503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10119216322049092668440335 15178824483073639002660503)
              ·
                refine ⟨22768236724610458503990755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15178824483073639002660503 22768236724610458503990755)
                ·
                  refine ⟨34152355086915687755986133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22768236724610458503990755 34152355086915687755986133)
                  ·
                    refine ⟨800445822349586431780925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34152355086915687755986133 800445822349586431780925)
                    ·
                      rfl

theorem cell22_2338294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2338294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338294 prefixEnd_2338294 := by exact prefixLift 2338294
  have htrace : WordTrace (prefixWord ++ tailWord_2338294) baseStart_2338294 baseEnd_2338294 := by
    simpa [prefixWord, tailWord_2338294, baseEnd_2338294] using wordTrace_append hprefix tailTrace_2338294
  have hstable : (prefixWord ++ tailWord_2338294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338294).length < 2 ^ (prefixWord ++ tailWord_2338294).sum := by decide
  have hdescent : baseEnd_2338294 < baseStart_2338294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338309 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2338309 : Nat := 118140960795 + 2338309 * 2 ^ 59
def prefixEnd_2338309 : Nat := 4983230072969 + 3 ^ 40 * 2338309 * 2
def baseEnd_2338309 : Nat := 800450957156131392655879

theorem tailTrace_2338309 : CollatzResearch.WordTrace tailWord_2338309 prefixEnd_2338309 800450957156131392655879 := by
  unfold tailWord_2338309
  simp only [CollatzResearch.WordTrace]
  refine ⟨85285135685713319228321981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56856757123808879485547987 85285135685713319228321981)
  ·
    refine ⟨31981925882142494710620743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85285135685713319228321981 31981925882142494710620743)
    ·
      refine ⟨47972888823213742065931115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31981925882142494710620743 47972888823213742065931115)
      ·
        refine ⟨71959333234820613098896673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47972888823213742065931115 71959333234820613098896673)
        ·
          refine ⟨53969499926115459824172505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71959333234820613098896673 53969499926115459824172505)
          ·
            refine ⟨40477124944586594868129379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53969499926115459824172505 40477124944586594868129379)
            ·
              refine ⟨60715687416879892302194069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40477124944586594868129379 60715687416879892302194069)
              ·
                refine ⟨2846047847666244951665347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60715687416879892302194069 2846047847666244951665347)
                ·
                  refine ⟨4269071771499367427498021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846047847666244951665347 4269071771499367427498021)
                  ·
                    refine ⟨800450957156131392655879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4269071771499367427498021 800450957156131392655879)
                    ·
                      rfl

theorem cell22_2338309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2338309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338309 prefixEnd_2338309 := by exact prefixLift 2338309
  have htrace : WordTrace (prefixWord ++ tailWord_2338309) baseStart_2338309 baseEnd_2338309 := by
    simpa [prefixWord, tailWord_2338309, baseEnd_2338309] using wordTrace_append hprefix tailTrace_2338309
  have hstable : (prefixWord ++ tailWord_2338309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338309).length < 2 ^ (prefixWord ++ tailWord_2338309).sum := by decide
  have hdescent : baseEnd_2338309 < baseStart_2338309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338352 : List Nat := [2, 1, 1, 1, 2, 3, 1, 11]
def baseStart_2338352 : Nat := 118140960795 + 2338352 * 2 ^ 59
def prefixEnd_2338352 : Nat := 4983230072969 + 3 ^ 40 * 2338352 * 2
def baseEnd_2338352 : Nat := 88940630770543734870083

theorem tailTrace_2338352 : CollatzResearch.WordTrace tailWord_2338352 prefixEnd_2338352 88940630770543734870083 := by
  unfold tailWord_2338352
  simp only [CollatzResearch.WordTrace]
  refine ⟨42643352012278768786068655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56857802683038358381424873 42643352012278768786068655)
  ·
    refine ⟨63965028018418153179102983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42643352012278768786068655 63965028018418153179102983)
    ·
      refine ⟨95947542027627229768654475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63965028018418153179102983 95947542027627229768654475)
      ·
        refine ⟨143921313041440844652981713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95947542027627229768654475 143921313041440844652981713)
        ·
          refine ⟨107940984781080633489736285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143921313041440844652981713 107940984781080633489736285)
          ·
            refine ⟨40477869292905237558651107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107940984781080633489736285 40477869292905237558651107)
            ·
              refine ⟨60716803939357856337976661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40477869292905237558651107 60716803939357856337976661)
              ·
                refine ⟨88940630770543734870083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 60716803939357856337976661 88940630770543734870083)
                ·
                  rfl

theorem cell22_2338352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_2338352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338352 prefixEnd_2338352 := by exact prefixLift 2338352
  have htrace : WordTrace (prefixWord ++ tailWord_2338352) baseStart_2338352 baseEnd_2338352 := by
    simpa [prefixWord, tailWord_2338352, baseEnd_2338352] using wordTrace_append hprefix tailTrace_2338352
  have hstable : (prefixWord ++ tailWord_2338352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338352).length < 2 ^ (prefixWord ++ tailWord_2338352).sum := by decide
  have hdescent : baseEnd_2338352 < baseStart_2338352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338369 : List Nat := [1, 2, 5, 1, 1, 1, 3, 8]
def baseStart_2338369 : Nat := 118140960795 + 2338369 * 2 ^ 59
def prefixEnd_2338369 : Nat := 4983230072969 + 3 ^ 40 * 2338369 * 2
def baseEnd_2338369 : Nat := 88941277375812359572855

theorem tailTrace_2338369 : CollatzResearch.WordTrace tailWord_2338369 prefixEnd_2338369 88941277375812359572855 := by
  unfold tailWord_2338369
  simp only [CollatzResearch.WordTrace]
  refine ⟨85287324065495949475506161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56858216043663966317004107 85287324065495949475506161)
  ·
    refine ⟨63965493049121962106629621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85287324065495949475506161 63965493049121962106629621)
    ·
      refine ⟨5996764973355183947496527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63965493049121962106629621 5996764973355183947496527)
      ·
        refine ⟨8995147460032775921244791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5996764973355183947496527 8995147460032775921244791)
        ·
          refine ⟨13492721190049163881867187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8995147460032775921244791 13492721190049163881867187)
          ·
            refine ⟨20239081785073745822800781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13492721190049163881867187 20239081785073745822800781)
            ·
              refine ⟨7589655669402654683550293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20239081785073745822800781 7589655669402654683550293)
              ·
                refine ⟨88941277375812359572855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7589655669402654683550293 88941277375812359572855)
                ·
                  rfl

theorem cell22_2338369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 8].length) (baseStart_2338369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338369 prefixEnd_2338369 := by exact prefixLift 2338369
  have htrace : WordTrace (prefixWord ++ tailWord_2338369) baseStart_2338369 baseEnd_2338369 := by
    simpa [prefixWord, tailWord_2338369, baseEnd_2338369] using wordTrace_append hprefix tailTrace_2338369
  have hstable : (prefixWord ++ tailWord_2338369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338369).length < 2 ^ (prefixWord ++ tailWord_2338369).sum := by decide
  have hdescent : baseEnd_2338369 < baseStart_2338369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338375 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 4]
def baseStart_2338375 : Nat := 118140960795 + 2338375 * 2 ^ 59
def prefixEnd_2338375 : Nat := 4983230072969 + 3 ^ 40 * 2338375 * 2
def baseEnd_2338375 : Nat := 266824516768309740168559

theorem tailTrace_2338375 : CollatzResearch.WordTrace tailWord_2338375 prefixEnd_2338375 266824516768309740168559 := by
  unfold tailWord_2338375
  simp only [CollatzResearch.WordTrace]
  refine ⟨85287542903474212500224579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56858361935649475000149719 85287542903474212500224579)
  ·
    refine ⟨127931314355211318750336869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85287542903474212500224579 127931314355211318750336869)
    ·
      refine ⟨23987121441602122265688163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127931314355211318750336869 23987121441602122265688163)
      ·
        refine ⟨35980682162403183398532245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23987121441602122265688163 35980682162403183398532245)
        ·
          refine ⟨1686594476362649221806199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35980682162403183398532245 1686594476362649221806199)
          ·
            refine ⟨2529891714543973832709299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1686594476362649221806199 2529891714543973832709299)
            ·
              refine ⟨3794837571815960749063949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2529891714543973832709299 3794837571815960749063949)
              ·
                refine ⟨1423064089430985280898981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3794837571815960749063949 1423064089430985280898981)
                ·
                  refine ⟨266824516768309740168559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423064089430985280898981 266824516768309740168559)
                  ·
                    rfl

theorem cell22_2338375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 4].length) (baseStart_2338375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338375 prefixEnd_2338375 := by exact prefixLift 2338375
  have htrace : WordTrace (prefixWord ++ tailWord_2338375) baseStart_2338375 baseEnd_2338375 := by
    simpa [prefixWord, tailWord_2338375, baseEnd_2338375] using wordTrace_append hprefix tailTrace_2338375
  have hstable : (prefixWord ++ tailWord_2338375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338375).length < 2 ^ (prefixWord ++ tailWord_2338375).sum := by decide
  have hdescent : baseEnd_2338375 < baseStart_2338375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338452 : List Nat := [2, 4, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2338452 : Nat := 118140960795 + 2338452 * 2 ^ 59
def prefixEnd_2338452 : Nat := 4983230072969 + 3 ^ 40 * 2338452 * 2
def baseEnd_2338452 : Nat := 800499908978526686330441

theorem tailTrace_2338452 : CollatzResearch.WordTrace tailWord_2338452 prefixEnd_2338452 800499908978526686330441 := by
  unfold tailWord_2338452
  simp only [CollatzResearch.WordTrace]
  refine ⟨42645175662097627325388805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56860234216130169767185073 42645175662097627325388805)
  ·
    refine ⟨7995970436643305123510401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42645175662097627325388805 7995970436643305123510401)
    ·
      refine ⟨5996977827482478842632801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7995970436643305123510401 5996977827482478842632801)
      ·
        refine ⟨4497733370611859131974601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5996977827482478842632801 4497733370611859131974601)
        ·
          refine ⟨3373300027958894348980951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4497733370611859131974601 3373300027958894348980951)
          ·
            refine ⟨5059950041938341523471427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373300027958894348980951 5059950041938341523471427)
            ·
              refine ⟨7589925062907512285207141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059950041938341523471427 7589925062907512285207141)
              ·
                refine ⟨1423110949295158553476339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7589925062907512285207141 1423110949295158553476339)
                ·
                  refine ⟨2134666423942737830214509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423110949295158553476339 2134666423942737830214509)
                  ·
                    refine ⟨800499908978526686330441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134666423942737830214509 800499908978526686330441)
                    ·
                      rfl

theorem cell22_2338452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2338452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338452 prefixEnd_2338452 := by exact prefixLift 2338452
  have htrace : WordTrace (prefixWord ++ tailWord_2338452) baseStart_2338452 baseEnd_2338452 := by
    simpa [prefixWord, tailWord_2338452, baseEnd_2338452] using wordTrace_append hprefix tailTrace_2338452
  have hstable : (prefixWord ++ tailWord_2338452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338452).length < 2 ^ (prefixWord ++ tailWord_2338452).sum := by decide
  have hdescent : baseEnd_2338452 < baseStart_2338452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338463 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 5]
def baseStart_2338463 : Nat := 118140960795 + 2338463 * 2 ^ 59
def prefixEnd_2338463 : Nat := 4983230072969 + 3 ^ 40 * 2338463 * 2
def baseEnd_2338463 : Nat := 800503674503326324305407

theorem tailTrace_2338463 : CollatzResearch.WordTrace tailWord_2338463 prefixEnd_2338463 800503674503326324305407 := by
  unfold tailWord_2338463
  simp only [CollatzResearch.WordTrace]
  refine ⟨85290752527155403529428043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56860501684770269019618695 85290752527155403529428043)
  ·
    refine ⟨127936128790733105294142065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85290752527155403529428043 127936128790733105294142065)
    ·
      refine ⟨95952096593049828970606549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127936128790733105294142065 95952096593049828970606549)
      ·
        refine ⟨2248877263899605366498591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 95952096593049828970606549 2248877263899605366498591)
        ·
          refine ⟨3373315895849408049747887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248877263899605366498591 3373315895849408049747887)
          ·
            refine ⟨5059973843774112074621831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3373315895849408049747887 5059973843774112074621831)
            ·
              refine ⟨7589960765661168111932747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5059973843774112074621831 7589960765661168111932747)
              ·
                refine ⟨11384941148491752167899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7589960765661168111932747 11384941148491752167899121)
                ·
                  refine ⟨8538705861368814125924341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11384941148491752167899121 8538705861368814125924341)
                  ·
                    refine ⟨800503674503326324305407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8538705861368814125924341 800503674503326324305407)
                    ·
                      rfl

theorem cell22_2338463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_2338463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338463 prefixEnd_2338463 := by exact prefixLift 2338463
  have htrace : WordTrace (prefixWord ++ tailWord_2338463) baseStart_2338463 baseEnd_2338463 := by
    simpa [prefixWord, tailWord_2338463, baseEnd_2338463] using wordTrace_append hprefix tailTrace_2338463
  have hstable : (prefixWord ++ tailWord_2338463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338463).length < 2 ^ (prefixWord ++ tailWord_2338463).sum := by decide
  have hdescent : baseEnd_2338463 < baseStart_2338463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338493 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2338493 : Nat := 118140960795 + 2338493 * 2 ^ 59
def prefixEnd_2338493 : Nat := 4983230072969 + 3 ^ 40 * 2338493 * 2
def baseEnd_2338493 : Nat := 266837981372138748685105

theorem tailTrace_2338493 : CollatzResearch.WordTrace tailWord_2338493 prefixEnd_2338493 266837981372138748685105 := by
  unfold tailWord_2338493
  simp only [CollatzResearch.WordTrace]
  refine ⟨85291846717046718653020133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56861231144697812435346755 85291846717046718653020133)
  ·
    refine ⟨15992221259446259747441275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85291846717046718653020133 15992221259446259747441275)
    ·
      refine ⟨23988331889169389621161913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15992221259446259747441275 23988331889169389621161913)
      ·
        refine ⟨17991248916877042215871435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23988331889169389621161913 17991248916877042215871435)
        ·
          refine ⟨26986873375315563323807153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17991248916877042215871435 26986873375315563323807153)
          ·
            refine ⟨20240155031486672492855365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26986873375315563323807153 20240155031486672492855365)
            ·
              refine ⟨3795029068403751092410381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20240155031486672492855365 3795029068403751092410381)
              ·
                refine ⟨1423135900651406659653893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3795029068403751092410381 1423135900651406659653893)
                ·
                  refine ⟨266837981372138748685105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423135900651406659653893 266837981372138748685105)
                  ·
                    rfl

theorem cell22_2338493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2338493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338493 prefixEnd_2338493 := by exact prefixLift 2338493
  have htrace : WordTrace (prefixWord ++ tailWord_2338493) baseStart_2338493 baseEnd_2338493 := by
    simpa [prefixWord, tailWord_2338493, baseEnd_2338493] using wordTrace_append hprefix tailTrace_2338493
  have hstable : (prefixWord ++ tailWord_2338493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338493).length < 2 ^ (prefixWord ++ tailWord_2338493).sum := by decide
  have hdescent : baseEnd_2338493 < baseStart_2338493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338504 : List Nat := [2, 1, 3, 1, 2, 2, 11]
def baseStart_2338504 : Nat := 118140960795 + 2338504 * 2 ^ 59
def prefixEnd_2338504 : Nat := 4983230072969 + 3 ^ 40 * 2338504 * 2
def baseEnd_2338504 : Nat := 29648804060785773482603

theorem tailTrace_2338504 : CollatzResearch.WordTrace tailWord_2338504 prefixEnd_2338504 29648804060785773482603 := by
  unfold tailWord_2338504
  simp only [CollatzResearch.WordTrace]
  refine ⟨42646123960003433765835283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56861498613337911687780377 42646123960003433765835283)
  ·
    refine ⟨63969185940005150648752925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42646123960003433765835283 63969185940005150648752925)
    ·
      refine ⟨23988444727501931493282347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63969185940005150648752925 23988444727501931493282347)
      ·
        refine ⟨35982667091252897239923521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23988444727501931493282347 35982667091252897239923521)
        ·
          refine ⟨26987000318439672929942641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35982667091252897239923521 26987000318439672929942641)
          ·
            refine ⟨20240250238829754697456981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26987000318439672929942641 20240250238829754697456981)
            ·
              refine ⟨29648804060785773482603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20240250238829754697456981 29648804060785773482603)
              ·
                rfl

theorem cell22_2338504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 11].length) (baseStart_2338504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338504 prefixEnd_2338504 := by exact prefixLift 2338504
  have htrace : WordTrace (prefixWord ++ tailWord_2338504) baseStart_2338504 baseEnd_2338504 := by
    simpa [prefixWord, tailWord_2338504, baseEnd_2338504] using wordTrace_append hprefix tailTrace_2338504
  have hstable : (prefixWord ++ tailWord_2338504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338504).length < 2 ^ (prefixWord ++ tailWord_2338504).sum := by decide
  have hdescent : baseEnd_2338504 < baseStart_2338504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338570 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2338570 : Nat := 118140960795 + 2338570 * 2 ^ 59
def prefixEnd_2338570 : Nat := 4983230072969 + 3 ^ 40 * 2338570 * 2
def baseEnd_2338570 : Nat := 800540302790013711880079

theorem tailTrace_2338570 : CollatzResearch.WordTrace tailWord_2338570 prefixEnd_2338570 800540302790013711880079 := by
  unfold tailWord_2338570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21323663784441940200893291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56863103425178507202382109 21323663784441940200893291)
  ·
    refine ⟨31985495676662910301339937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21323663784441940200893291 31985495676662910301339937)
    ·
      refine ⟨23989121757497182726004953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31985495676662910301339937 23989121757497182726004953)
      ·
        refine ⟨17991841318122887044503715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23989121757497182726004953 17991841318122887044503715)
        ·
          refine ⟨26987761977184330566755573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17991841318122887044503715 26987761977184330566755573)
          ·
            refine ⟨2530102685361030990633335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26987761977184330566755573 2530102685361030990633335)
            ·
              refine ⟨3795154028041546485950003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530102685361030990633335 3795154028041546485950003)
              ·
                refine ⟨5692731042062319728925005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795154028041546485950003 5692731042062319728925005)
                ·
                  refine ⟨2134774140773369898346877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5692731042062319728925005 2134774140773369898346877)
                  ·
                    refine ⟨800540302790013711880079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2134774140773369898346877 800540302790013711880079)
                    ·
                      rfl

theorem cell22_2338570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2338570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338570 prefixEnd_2338570 := by exact prefixLift 2338570
  have htrace : WordTrace (prefixWord ++ tailWord_2338570) baseStart_2338570 baseEnd_2338570 := by
    simpa [prefixWord, tailWord_2338570, baseEnd_2338570] using wordTrace_append hprefix tailTrace_2338570
  have hstable : (prefixWord ++ tailWord_2338570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338570).length < 2 ^ (prefixWord ++ tailWord_2338570).sum := by decide
  have hdescent : baseEnd_2338570 < baseStart_2338570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338583 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 5]
def baseStart_2338583 : Nat := 118140960795 + 2338583 * 2 ^ 59
def prefixEnd_2338583 : Nat := 4983230072969 + 3 ^ 40 * 2338583 * 2
def baseEnd_2338583 : Nat := 266848250985228670435013

theorem tailTrace_2338583 : CollatzResearch.WordTrace tailWord_2338583 prefixEnd_2338583 266848250985228670435013 := by
  unfold tailWord_2338583
  simp only [CollatzResearch.WordTrace]
  refine ⟨85295129286720664023796403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56863419524480442682530935 85295129286720664023796403)
  ·
    refine ⟨127942693930080996035694605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85295129286720664023796403 127942693930080996035694605)
    ·
      refine ⟨47978510223780373513385477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127942693930080996035694605 47978510223780373513385477)
      ·
        refine ⟨8995970666958820033759777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47978510223780373513385477 8995970666958820033759777)
        ·
          refine ⟨6746978000219115025319833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8995970666958820033759777 6746978000219115025319833)
          ·
            refine ⟨5060233500164336268989875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6746978000219115025319833 5060233500164336268989875)
            ·
              refine ⟨7590350250246504403484813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5060233500164336268989875 7590350250246504403484813)
              ·
                refine ⟨2846381343842439151306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7590350250246504403484813 2846381343842439151306805)
                ·
                  refine ⟨266848250985228670435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2846381343842439151306805 266848250985228670435013)
                  ·
                    rfl

theorem cell22_2338583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 5].length) (baseStart_2338583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338583 prefixEnd_2338583 := by exact prefixLift 2338583
  have htrace : WordTrace (prefixWord ++ tailWord_2338583) baseStart_2338583 baseEnd_2338583 := by
    simpa [prefixWord, tailWord_2338583, baseEnd_2338583] using wordTrace_append hprefix tailTrace_2338583
  have hstable : (prefixWord ++ tailWord_2338583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338583).length < 2 ^ (prefixWord ++ tailWord_2338583).sum := by decide
  have hdescent : baseEnd_2338583 < baseStart_2338583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338808 : List Nat := [2, 1, 2, 1, 1, 3, 5, 7]
def baseStart_2338808 : Nat := 118140960795 + 2338808 * 2 ^ 59
def prefixEnd_2338808 : Nat := 4983230072969 + 3 ^ 40 * 2338808 * 2
def baseEnd_2338808 : Nat := 88957975005984491603261

theorem tailTrace_2338808 : CollatzResearch.WordTrace tailWord_2338808 prefixEnd_2338808 88957975005984491603261 := by
  unfold tailWord_2338808
  simp only [CollatzResearch.WordTrace]
  refine ⟨42651667855452763725368539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56868890473937018300491385 42651667855452763725368539)
  ·
    refine ⟨63977501783179145588052809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42651667855452763725368539 63977501783179145588052809)
    ·
      refine ⟨47983126337384359191039607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63977501783179145588052809 47983126337384359191039607)
      ·
        refine ⟨71974689506076538786559411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47983126337384359191039607 71974689506076538786559411)
        ·
          refine ⟨107962034259114808179839117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71974689506076538786559411 107962034259114808179839117)
          ·
            refine ⟨40485762847168053067439669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107962034259114808179839117 40485762847168053067439669)
            ·
              refine ⟨3795540266922004975072469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40485762847168053067439669 3795540266922004975072469)
              ·
                refine ⟨88957975005984491603261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3795540266922004975072469 88957975005984491603261)
                ·
                  rfl

theorem cell22_2338808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_2338808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338808 prefixEnd_2338808 := by exact prefixLift 2338808
  have htrace : WordTrace (prefixWord ++ tailWord_2338808) baseStart_2338808 baseEnd_2338808 := by
    simpa [prefixWord, tailWord_2338808, baseEnd_2338808] using wordTrace_append hprefix tailTrace_2338808
  have hstable : (prefixWord ++ tailWord_2338808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338808).length < 2 ^ (prefixWord ++ tailWord_2338808).sum := by decide
  have hdescent : baseEnd_2338808 < baseStart_2338808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338840 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_2338840 : Nat := 118140960795 + 2338840 * 2 ^ 59
def prefixEnd_2338840 : Nat := 4983230072969 + 3 ^ 40 * 2338840 * 2
def baseEnd_2338840 : Nat := 800632729307823007629251

theorem tailTrace_2338840 : CollatzResearch.WordTrace tailWord_2338840 prefixEnd_2338840 800632729307823007629251 := by
  unfold tailWord_2338840
  simp only [CollatzResearch.WordTrace]
  refine ⟨42652251423394798457950987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56869668564526397943934649 42652251423394798457950987)
  ·
    refine ⟨63978377135092197686926481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42652251423394798457950987 63978377135092197686926481)
    ·
      refine ⟨47983782851319148265194861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63978377135092197686926481 47983782851319148265194861)
      ·
        refine ⟨17993918569244680599448073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47983782851319148265194861 17993918569244680599448073)
        ·
          refine ⟨13495438926933510449586055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17993918569244680599448073 13495438926933510449586055)
          ·
            refine ⟨20243158390400265674379083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13495438926933510449586055 20243158390400265674379083)
            ·
              refine ⟨30364737585600398511568625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20243158390400265674379083 30364737585600398511568625)
              ·
                refine ⟨22773553189200298883676469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30364737585600398511568625 22773553189200298883676469)
                ·
                  refine ⟨2135020611487528020344669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22773553189200298883676469 2135020611487528020344669)
                  ·
                    refine ⟨800632729307823007629251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135020611487528020344669 800632729307823007629251)
                    ·
                      rfl

theorem cell22_2338840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_2338840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338840 prefixEnd_2338840 := by exact prefixLift 2338840
  have htrace : WordTrace (prefixWord ++ tailWord_2338840) baseStart_2338840 baseEnd_2338840 := by
    simpa [prefixWord, tailWord_2338840, baseEnd_2338840] using wordTrace_append hprefix tailTrace_2338840
  have hstable : (prefixWord ++ tailWord_2338840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338840).length < 2 ^ (prefixWord ++ tailWord_2338840).sum := by decide
  have hdescent : baseEnd_2338840 < baseStart_2338840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_2338900 : Nat := 118140960795 + 2338900 * 2 ^ 59
def prefixEnd_2338900 : Nat := 4983230072969 + 3 ^ 40 * 2338900 * 2
def baseEnd_2338900 : Nat := 800653268534002851129067

theorem tailTrace_2338900 : CollatzResearch.WordTrace tailWord_2338900 prefixEnd_2338900 800653268534002851129067 := by
  unfold tailWord_2338900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42653345613286113581543077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56871127484381484775390769 42653345613286113581543077)
  ·
    refine ⟨7997502302491146296539327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42653345613286113581543077 7997502302491146296539327)
    ·
      refine ⟨11996253453736719444808991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997502302491146296539327 11996253453736719444808991)
      ·
        refine ⟨17994380180605079167213487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11996253453736719444808991 17994380180605079167213487)
        ·
          refine ⟨26991570270907618750820231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17994380180605079167213487 26991570270907618750820231)
          ·
            refine ⟨40487355406361428126230347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26991570270907618750820231 40487355406361428126230347)
            ·
              refine ⟨60731033109542142189345521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40487355406361428126230347 60731033109542142189345521)
              ·
                refine ⟨45548274832156606642009141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60731033109542142189345521 45548274832156606642009141)
                ·
                  refine ⟨4270150765514681872688357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45548274832156606642009141 4270150765514681872688357)
                  ·
                    refine ⟨800653268534002851129067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270150765514681872688357 800653268534002851129067)
                    ·
                      rfl

theorem cell22_2338900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_2338900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338900 prefixEnd_2338900 := by exact prefixLift 2338900
  have htrace : WordTrace (prefixWord ++ tailWord_2338900) baseStart_2338900 baseEnd_2338900 := by
    simpa [prefixWord, tailWord_2338900, baseEnd_2338900] using wordTrace_append hprefix tailTrace_2338900
  have hstable : (prefixWord ++ tailWord_2338900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338900).length < 2 ^ (prefixWord ++ tailWord_2338900).sum := by decide
  have hdescent : baseEnd_2338900 < baseStart_2338900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338915 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 6]
def baseStart_2338915 : Nat := 118140960795 + 2338915 * 2 ^ 59
def prefixEnd_2338915 : Nat := 4983230072969 + 3 ^ 40 * 2338915 * 2
def baseEnd_2338915 : Nat := 266886134446849270668007

theorem tailTrace_2338915 : CollatzResearch.WordTrace tailWord_2338915 prefixEnd_2338915 266886134446849270668007 := by
  unfold tailWord_2338915
  simp only [CollatzResearch.WordTrace]
  refine ⟨85307238321517884724882199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56871492214345256483254799 85307238321517884724882199)
  ·
    refine ⟨127960857482276827087323299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85307238321517884724882199 127960857482276827087323299)
    ·
      refine ⟨191941286223415240630984949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127960857482276827087323299 191941286223415240630984949)
      ·
        refine ⟨17994495583445178809154839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191941286223415240630984949 17994495583445178809154839)
        ·
          refine ⟨26991743375167768213732259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17994495583445178809154839 26991743375167768213732259)
          ·
            refine ⟨40487615062751652320598389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26991743375167768213732259 40487615062751652320598389)
            ·
              refine ⟨3795713912132967405056099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40487615062751652320598389 3795713912132967405056099)
              ·
                refine ⟨5693570868199451107584149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795713912132967405056099 5693570868199451107584149)
                ·
                  refine ⟨266886134446849270668007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5693570868199451107584149 266886134446849270668007)
                  ·
                    rfl

theorem cell22_2338915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_2338915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338915 prefixEnd_2338915 := by exact prefixLift 2338915
  have htrace : WordTrace (prefixWord ++ tailWord_2338915) baseStart_2338915 baseEnd_2338915 := by
    simpa [prefixWord, tailWord_2338915, baseEnd_2338915] using wordTrace_append hprefix tailTrace_2338915
  have hstable : (prefixWord ++ tailWord_2338915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338915).length < 2 ^ (prefixWord ++ tailWord_2338915).sum := by decide
  have hdescent : baseEnd_2338915 < baseStart_2338915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338934 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_2338934 : Nat := 118140960795 + 2338934 * 2 ^ 59
def prefixEnd_2338934 : Nat := 4983230072969 + 3 ^ 40 * 2338934 * 2
def baseEnd_2338934 : Nat := 800664907428838095778963

theorem tailTrace_2338934 : CollatzResearch.WordTrace tailWord_2338934 prefixEnd_2338934 800664907428838095778963 := by
  unfold tailWord_2338934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331745706778065685613991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56871954205632700646549237 5331745706778065685613991)
  ·
    refine ⟨7997618560167098528420987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5331745706778065685613991 7997618560167098528420987)
    ·
      refine ⟨11996427840250647792631481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7997618560167098528420987 11996427840250647792631481)
      ·
        refine ⟨8997320880187985844473611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11996427840250647792631481 8997320880187985844473611)
        ·
          refine ⟨13495981320281978766710417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8997320880187985844473611 13495981320281978766710417)
          ·
            refine ⟨10121985990211484075032813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13495981320281978766710417 10121985990211484075032813)
            ·
              refine ⟨3795744746329306528137305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10121985990211484075032813 3795744746329306528137305)
              ·
                refine ⟨2846808559746979896102979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3795744746329306528137305 2846808559746979896102979)
                ·
                  refine ⟨4270212839620469844154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2846808559746979896102979 4270212839620469844154469)
                  ·
                    refine ⟨800664907428838095778963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270212839620469844154469 800664907428838095778963)
                    ·
                      rfl

theorem cell22_2338934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_2338934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338934 prefixEnd_2338934 := by exact prefixLift 2338934
  have htrace : WordTrace (prefixWord ++ tailWord_2338934) baseStart_2338934 baseEnd_2338934 := by
    simpa [prefixWord, tailWord_2338934, baseEnd_2338934] using wordTrace_append hprefix tailTrace_2338934
  have hstable : (prefixWord ++ tailWord_2338934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338934).length < 2 ^ (prefixWord ++ tailWord_2338934).sum := by decide
  have hdescent : baseEnd_2338934 < baseStart_2338934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338962 : List Nat := [3, 2, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2338962 : Nat := 118140960795 + 2338962 * 2 ^ 59
def prefixEnd_2338962 : Nat := 4983230072969 + 3 ^ 40 * 2338962 * 2
def baseEnd_2338962 : Nat := 800674492401055356078877

theorem tailTrace_2338962 : CollatzResearch.WordTrace tailWord_2338962 prefixEnd_2338962 800674492401055356078877 := by
  unfold tailWord_2338962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21327238138086902937960785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56872635034898407834562093 21327238138086902937960785)
  ·
    refine ⟨15995428603565177203470589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21327238138086902937960785 15995428603565177203470589)
    ·
      refine ⟨5998285726336941451301471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15995428603565177203470589 5998285726336941451301471)
      ·
        refine ⟨8997428589505412176952207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5998285726336941451301471 8997428589505412176952207)
        ·
          refine ⟨13496142884258118265428311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8997428589505412176952207 13496142884258118265428311)
          ·
            refine ⟨20244214326387177398142467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13496142884258118265428311 20244214326387177398142467)
            ·
              refine ⟨30366321489580766097213701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20244214326387177398142467 30366321489580766097213701)
              ·
                refine ⟨5693685279296393643227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30366321489580766097213701 5693685279296393643227569)
                ·
                  refine ⟨4270263959472295232420677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693685279296393643227569 4270263959472295232420677)
                  ·
                    refine ⟨800674492401055356078877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270263959472295232420677 800674492401055356078877)
                    ·
                      rfl

theorem cell22_2338962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2338962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338962 prefixEnd_2338962 := by exact prefixLift 2338962
  have htrace : WordTrace (prefixWord ++ tailWord_2338962) baseStart_2338962 baseEnd_2338962 := by
    simpa [prefixWord, tailWord_2338962, baseEnd_2338962] using wordTrace_append hprefix tailTrace_2338962
  have hstable : (prefixWord ++ tailWord_2338962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338962).length < 2 ^ (prefixWord ++ tailWord_2338962).sum := by decide
  have hdescent : baseEnd_2338962 < baseStart_2338962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2338977 : List Nat := [1, 2, 3, 3, 1, 4, 1, 7]
def baseStart_2338977 : Nat := 118140960795 + 2338977 * 2 ^ 59
def prefixEnd_2338977 : Nat := 4983230072969 + 3 ^ 40 * 2338977 * 2
def baseEnd_2338977 : Nat := 88964403023066701883759

theorem tailTrace_2338977 : CollatzResearch.WordTrace tailWord_2338977 prefixEnd_2338977 88964403023066701883759 := by
  unfold tailWord_2338977
  simp only [CollatzResearch.WordTrace]
  refine ⟨85309499647293269313639185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56872999764862179542426123 85309499647293269313639185)
  ·
    refine ⟨63982124735469951985229389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85309499647293269313639185 63982124735469951985229389)
    ·
      refine ⟨23993296775801231994461021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63982124735469951985229389 23993296775801231994461021)
      ·
        refine ⟨8997486290925461997922883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23993296775801231994461021 8997486290925461997922883)
        ·
          refine ⟨13496229436388192996884325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8997486290925461997922883 13496229436388192996884325)
          ·
            refine ⟨2530543019322786186915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13496229436388192996884325 2530543019322786186915811)
            ·
              refine ⟨3795814528984179280373717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530543019322786186915811 3795814528984179280373717)
              ·
                refine ⟨88964403023066701883759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3795814528984179280373717 88964403023066701883759)
                ·
                  rfl

theorem cell22_2338977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 7].length) (baseStart_2338977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2338977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2338977 prefixEnd_2338977 := by exact prefixLift 2338977
  have htrace : WordTrace (prefixWord ++ tailWord_2338977) baseStart_2338977 baseEnd_2338977 := by
    simpa [prefixWord, tailWord_2338977, baseEnd_2338977] using wordTrace_append hprefix tailTrace_2338977
  have hstable : (prefixWord ++ tailWord_2338977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2338977).length < 2 ^ (prefixWord ++ tailWord_2338977).sum := by decide
  have hdescent : baseEnd_2338977 < baseStart_2338977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2338977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339005 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2339005 : Nat := 118140960795 + 2339005 * 2 ^ 59
def prefixEnd_2339005 : Nat := 4983230072969 + 3 ^ 40 * 2339005 * 2
def baseEnd_2339005 : Nat := 266896404059939192417915

theorem tailTrace_2339005 : CollatzResearch.WordTrace tailWord_2339005 prefixEnd_2339005 266896404059939192417915 := by
  unfold tailWord_2339005
  simp only [CollatzResearch.WordTrace]
  refine ⟨85310520891191830095658469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56873680594127886730438979 85310520891191830095658469)
  ·
    refine ⟨15995722667098468142935963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85310520891191830095658469 15995722667098468142935963)
    ·
      refine ⟨23993584000647702214403945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15995722667098468142935963 23993584000647702214403945)
      ·
        refine ⟨17995188000485776660802959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23993584000647702214403945 17995188000485776660802959)
        ·
          refine ⟨26992782000728664991204439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17995188000485776660802959 26992782000728664991204439)
          ·
            refine ⟨40489173001092997486806659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26992782000728664991204439 40489173001092997486806659)
            ·
              refine ⟨60733759501639496230209989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40489173001092997486806659 60733759501639496230209989)
              ·
                refine ⟨11387579906557405543164373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60733759501639496230209989 11387579906557405543164373)
                ·
                  refine ⟨266896404059939192417915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11387579906557405543164373 266896404059939192417915)
                  ·
                    rfl

theorem cell22_2339005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2339005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339005 prefixEnd_2339005 := by exact prefixLift 2339005
  have htrace : WordTrace (prefixWord ++ tailWord_2339005) baseStart_2339005 baseEnd_2339005 := by
    simpa [prefixWord, tailWord_2339005, baseEnd_2339005] using wordTrace_append hprefix tailTrace_2339005
  have hstable : (prefixWord ++ tailWord_2339005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339005).length < 2 ^ (prefixWord ++ tailWord_2339005).sum := by decide
  have hdescent : baseEnd_2339005 < baseStart_2339005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339022 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_2339022 : Nat := 118140960795 + 2339022 * 2 ^ 59
def prefixEnd_2339022 : Nat := 4983230072969 + 3 ^ 40 * 2339022 * 2
def baseEnd_2339022 : Nat := 266898343875745066526231

theorem tailTrace_2339022 : CollatzResearch.WordTrace tailWord_2339022 prefixEnd_2339022 266898343875745066526231 := by
  unfold tailWord_2339022
  simp only [CollatzResearch.WordTrace]
  refine ⟨10663892616516280249878415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56874093954753494666018213 10663892616516280249878415)
  ·
    refine ⟨15995838924774420374817623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10663892616516280249878415 15995838924774420374817623)
    ·
      refine ⟨23993758387161630562226435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15995838924774420374817623 23993758387161630562226435)
      ·
        refine ⟨35990637580742445843339653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23993758387161630562226435 35990637580742445843339653)
        ·
          refine ⟨6748244546389208595626185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35990637580742445843339653 6748244546389208595626185)
          ·
            refine ⟨5061183409791906446719639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6748244546389208595626185 5061183409791906446719639)
            ·
              refine ⟨7591775114687859670079459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061183409791906446719639 7591775114687859670079459)
              ·
                refine ⟨11387662672031789505119189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7591775114687859670079459 11387662672031789505119189)
                ·
                  refine ⟨266898343875745066526231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11387662672031789505119189 266898343875745066526231)
                  ·
                    rfl

theorem cell22_2339022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_2339022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339022 prefixEnd_2339022 := by exact prefixLift 2339022
  have htrace : WordTrace (prefixWord ++ tailWord_2339022) baseStart_2339022 baseEnd_2339022 := by
    simpa [prefixWord, tailWord_2339022, baseEnd_2339022] using wordTrace_append hprefix tailTrace_2339022
  have hstable : (prefixWord ++ tailWord_2339022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339022).length < 2 ^ (prefixWord ++ tailWord_2339022).sum := by decide
  have hdescent : baseEnd_2339022 < baseStart_2339022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339026 : List Nat := [3, 2, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_2339026 : Nat := 118140960795 + 2339026 * 2 ^ 59
def prefixEnd_2339026 : Nat := 4983230072969 + 3 ^ 40 * 2339026 * 2
def baseEnd_2339026 : Nat := 800696400908980522478681

theorem tailTrace_2339026 : CollatzResearch.WordTrace tailWord_2339026 prefixEnd_2339026 800696400908980522478681 := by
  unfold tailWord_2339026
  simp only [CollatzResearch.WordTrace]
  refine ⟨21327821706028937670543233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56874191216077167121448621 21327821706028937670543233)
  ·
    refine ⟨15995866279521703252907425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21327821706028937670543233 15995866279521703252907425)
    ·
      refine ⟨11996899709641277439680569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15995866279521703252907425 11996899709641277439680569)
      ·
        refine ⟨8997674782230958079760427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11996899709641277439680569 8997674782230958079760427)
        ·
          refine ⟨13496512173346437119640641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8997674782230958079760427 13496512173346437119640641)
          ·
            refine ⟨10122384130009827839730481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13496512173346437119640641 10122384130009827839730481)
            ·
              refine ⟨7591788097507370879797861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10122384130009827839730481 7591788097507370879797861)
              ·
                refine ⟨1423460268282632039962099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7591788097507370879797861 1423460268282632039962099)
                ·
                  refine ⟨2135190402423948059943149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423460268282632039962099 2135190402423948059943149)
                  ·
                    refine ⟨800696400908980522478681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135190402423948059943149 800696400908980522478681)
                    ·
                      rfl

theorem cell22_2339026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_2339026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339026 prefixEnd_2339026 := by exact prefixLift 2339026
  have htrace : WordTrace (prefixWord ++ tailWord_2339026) baseStart_2339026 baseEnd_2339026 := by
    simpa [prefixWord, tailWord_2339026, baseEnd_2339026] using wordTrace_append hprefix tailTrace_2339026
  have hstable : (prefixWord ++ tailWord_2339026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339026).length < 2 ^ (prefixWord ++ tailWord_2339026).sum := by decide
  have hdescent : baseEnd_2339026 < baseStart_2339026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339172 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2339172 : Nat := 118140960795 + 2339172 * 2 ^ 59
def prefixEnd_2339172 : Nat := 4983230072969 + 3 ^ 40 * 2339172 * 2
def baseEnd_2339172 : Nat := 800746379692684808328233

theorem tailTrace_2339172 : CollatzResearch.WordTrace tailWord_2339172 prefixEnd_2339172 800746379692684808328233 := by
  unfold tailWord_2339172
  simp only [CollatzResearch.WordTrace]
  refine ⟨42658305940793408808493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56877741254391211744658513 42658305940793408808493885)
  ·
    refine ⟨15996864727797528303185207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42658305940793408808493885 15996864727797528303185207)
    ·
      refine ⟨23995297091696292454777811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15996864727797528303185207 23995297091696292454777811)
      ·
        refine ⟨35992945637544438682166717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23995297091696292454777811 35992945637544438682166717)
        ·
          refine ⟨13497354614079164505812519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35992945637544438682166717 13497354614079164505812519)
          ·
            refine ⟨20246031921118746758718779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497354614079164505812519 20246031921118746758718779)
            ·
              refine ⟨30369047881678120138078169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20246031921118746758718779 30369047881678120138078169)
              ·
                refine ⟨22776785911258590103558627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30369047881678120138078169 22776785911258590103558627)
                ·
                  refine ⟨34165178866887885155337941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22776785911258590103558627 34165178866887885155337941)
                  ·
                    refine ⟨800746379692684808328233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34165178866887885155337941 800746379692684808328233)
                    ·
                      rfl

theorem cell22_2339172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2339172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339172 prefixEnd_2339172 := by exact prefixLift 2339172
  have htrace : WordTrace (prefixWord ++ tailWord_2339172) baseStart_2339172 baseEnd_2339172 := by
    simpa [prefixWord, tailWord_2339172, baseEnd_2339172] using wordTrace_append hprefix tailTrace_2339172
  have hstable : (prefixWord ++ tailWord_2339172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339172).length < 2 ^ (prefixWord ++ tailWord_2339172).sum := by decide
  have hdescent : baseEnd_2339172 < baseStart_2339172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339178 : List Nat := [3, 1, 3, 3, 1, 1, 1, 5, 1, 3]
def baseStart_2339178 : Nat := 118140960795 + 2339178 * 2 ^ 59
def prefixEnd_2339178 : Nat := 4983230072969 + 3 ^ 40 * 2339178 * 2
def baseEnd_2339178 : Nat := 800748433615302792678215

theorem tailTrace_2339178 : CollatzResearch.WordTrace tailWord_2339178 prefixEnd_2339178 800748433615302792678215 := by
  unfold tailWord_2339178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329207679891270160426547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56877887146376720427804125 21329207679891270160426547)
  ·
    refine ⟨31993811519836905240639821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21329207679891270160426547 31993811519836905240639821)
    ·
      refine ⟨11997679319938839465239933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31993811519836905240639821 11997679319938839465239933)
      ·
        refine ⟨4499129744977064799464975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11997679319938839465239933 4499129744977064799464975)
        ·
          refine ⟨6748694617465597199197463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499129744977064799464975 6748694617465597199197463)
          ·
            refine ⟨10123041926198395798796195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748694617465597199197463 10123041926198395798796195)
            ·
              refine ⟨15184562889297593698194293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123041926198395798796195 15184562889297593698194293)
              ·
                refine ⟨1423552770871649409205715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15184562889297593698194293 1423552770871649409205715)
                ·
                  refine ⟨2135329156307474113808573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423552770871649409205715 2135329156307474113808573)
                  ·
                    refine ⟨800748433615302792678215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135329156307474113808573 800748433615302792678215)
                    ·
                      rfl

theorem cell22_2339178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_2339178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339178 prefixEnd_2339178 := by exact prefixLift 2339178
  have htrace : WordTrace (prefixWord ++ tailWord_2339178) baseStart_2339178 baseEnd_2339178 := by
    simpa [prefixWord, tailWord_2339178, baseEnd_2339178] using wordTrace_append hprefix tailTrace_2339178
  have hstable : (prefixWord ++ tailWord_2339178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339178).length < 2 ^ (prefixWord ++ tailWord_2339178).sum := by decide
  have hdescent : baseEnd_2339178 < baseStart_2339178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339189 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2339189 : Nat := 118140960795 + 2339189 * 2 ^ 59
def prefixEnd_2339189 : Nat := 4983230072969 + 3 ^ 40 * 2339189 * 2
def baseEnd_2339189 : Nat := 800752199140102430653181

theorem tailTrace_2339189 : CollatzResearch.WordTrace tailWord_2339189 prefixEnd_2339189 800752199140102430653181 := by
  unfold tailWord_2339189
  simp only [CollatzResearch.WordTrace]
  refine ⟨85317231922525229520356621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56878154615016819680237747 85317231922525229520356621)
  ·
    refine ⟨31993961970946961070133733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85317231922525229520356621 31993961970946961070133733)
    ·
      refine ⟨5998867869552555200650075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31993961970946961070133733 5998867869552555200650075)
      ·
        refine ⟨8998301804328832800975113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5998867869552555200650075 8998301804328832800975113)
        ·
          refine ⟨6748726353246624600731335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8998301804328832800975113 6748726353246624600731335)
          ·
            refine ⟨10123089529869936901097003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6748726353246624600731335 10123089529869936901097003)
            ·
              refine ⟨15184634294804905351645505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123089529869936901097003 15184634294804905351645505)
              ·
                refine ⟨11388475721103679013734129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15184634294804905351645505 11388475721103679013734129)
                ·
                  refine ⟨8541356790827759260300597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11388475721103679013734129 8541356790827759260300597)
                  ·
                    refine ⟨800752199140102430653181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541356790827759260300597 800752199140102430653181)
                    ·
                      rfl

theorem cell22_2339189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2339189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339189 prefixEnd_2339189 := by exact prefixLift 2339189
  have htrace : WordTrace (prefixWord ++ tailWord_2339189) baseStart_2339189 baseEnd_2339189 := by
    simpa [prefixWord, tailWord_2339189, baseEnd_2339189] using wordTrace_append hprefix tailTrace_2339189
  have hstable : (prefixWord ++ tailWord_2339189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339189).length < 2 ^ (prefixWord ++ tailWord_2339189).sum := by decide
  have hdescent : baseEnd_2339189 < baseStart_2339189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339234 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_2339234 : Nat := 118140960795 + 2339234 * 2 ^ 59
def prefixEnd_2339234 : Nat := 4983230072969 + 3 ^ 40 * 2339234 * 2
def baseEnd_2339234 : Nat := 800767603559737313278043

theorem tailTrace_2339234 : CollatzResearch.WordTrace tailWord_2339234 prefixEnd_2339234 800767603559737313278043 := by
  unfold tailWord_2339234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21329718301840550551436189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56879248804908134803829837 21329718301840550551436189)
  ·
    refine ⟨7998644363190206456788571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21329718301840550551436189 7998644363190206456788571)
    ·
      refine ⟨11997966544785309685182857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7998644363190206456788571 11997966544785309685182857)
      ·
        refine ⟨8998474908588982263887143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11997966544785309685182857 8998474908588982263887143)
        ·
          refine ⟨13497712362883473395830715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998474908588982263887143 13497712362883473395830715)
          ·
            refine ⟨20246568544325210093746073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13497712362883473395830715 20246568544325210093746073)
            ·
              refine ⟨15184926408243907570309555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20246568544325210093746073 15184926408243907570309555)
              ·
                refine ⟨22777389612365861355464333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15184926408243907570309555 22777389612365861355464333)
                ·
                  refine ⟨8541521104637198008299125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22777389612365861355464333 8541521104637198008299125)
                  ·
                    refine ⟨800767603559737313278043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8541521104637198008299125 800767603559737313278043)
                    ·
                      rfl

theorem cell22_2339234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_2339234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339234 prefixEnd_2339234 := by exact prefixLift 2339234
  have htrace : WordTrace (prefixWord ++ tailWord_2339234) baseStart_2339234 baseEnd_2339234 := by
    simpa [prefixWord, tailWord_2339234, baseEnd_2339234] using wordTrace_append hprefix tailTrace_2339234
  have hstable : (prefixWord ++ tailWord_2339234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339234).length < 2 ^ (prefixWord ++ tailWord_2339234).sum := by decide
  have hdescent : baseEnd_2339234 < baseStart_2339234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339236 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_2339236 : Nat := 118140960795 + 2339236 * 2 ^ 59
def prefixEnd_2339236 : Nat := 4983230072969 + 3 ^ 40 * 2339236 * 2
def baseEnd_2339236 : Nat := 266922762733536658242679

theorem tailTrace_2339236 : CollatzResearch.WordTrace tailWord_2339236 prefixEnd_2339236 266922762733536658242679 := by
  unfold tailWord_2339236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42659473076677478273658781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56879297435569971031545041 42659473076677478273658781)
  ·
    refine ⟨15997302403754054352622043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42659473076677478273658781 15997302403754054352622043)
    ·
      refine ⟨23995953605631081528933065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15997302403754054352622043 23995953605631081528933065)
      ·
        refine ⟨17996965204223311146699799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23995953605631081528933065 17996965204223311146699799)
        ·
          refine ⟨26995447806334966720049699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17996965204223311146699799 26995447806334966720049699)
          ·
            refine ⟨40493171709502450080074549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26995447806334966720049699 40493171709502450080074549)
            ·
              refine ⟨3796234847765854695006989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40493171709502450080074549 3796234847765854695006989)
              ·
                refine ⟨1423588067912195510627621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3796234847765854695006989 1423588067912195510627621)
                ·
                  refine ⟨266922762733536658242679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423588067912195510627621 266922762733536658242679)
                  ·
                    rfl

theorem cell22_2339236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_2339236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339236 prefixEnd_2339236 := by exact prefixLift 2339236
  have htrace : WordTrace (prefixWord ++ tailWord_2339236) baseStart_2339236 baseEnd_2339236 := by
    simpa [prefixWord, tailWord_2339236, baseEnd_2339236] using wordTrace_append hprefix tailTrace_2339236
  have hstable : (prefixWord ++ tailWord_2339236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339236).length < 2 ^ (prefixWord ++ tailWord_2339236).sum := by decide
  have hdescent : baseEnd_2339236 < baseStart_2339236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339249 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2339249 : Nat := 118140960795 + 2339249 * 2 ^ 59
def prefixEnd_2339249 : Nat := 4983230072969 + 3 ^ 40 * 2339249 * 2
def baseEnd_2339249 : Nat := 800772738366282274152997

theorem tailTrace_2339249 : CollatzResearch.WordTrace tailWord_2339249 prefixEnd_2339249 800772738366282274152997 := by
  unfold tailWord_2339249
  simp only [CollatzResearch.WordTrace]
  refine ⟨85319420302307859767540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56879613534871906511693867 85319420302307859767540801)
  ·
    refine ⟨63989565226730894825655601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85319420302307859767540801 63989565226730894825655601)
    ·
      refine ⟨47992173920048171119241701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63989565226730894825655601 47992173920048171119241701)
      ·
        refine ⟨8998532610009032084857819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47992173920048171119241701 8998532610009032084857819)
        ·
          refine ⟨13497798915013548127286729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8998532610009032084857819 13497798915013548127286729)
          ·
            refine ⟨10123349186260161095465047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13497798915013548127286729 10123349186260161095465047)
            ·
              refine ⟨15185023779390241643197571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10123349186260161095465047 15185023779390241643197571)
              ·
                refine ⟨22777535669085362464796357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15185023779390241643197571 22777535669085362464796357)
                ·
                  refine ⟨4270787937953505462149317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22777535669085362464796357 4270787937953505462149317)
                  ·
                    refine ⟨800772738366282274152997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4270787937953505462149317 800772738366282274152997)
                    ·
                      rfl

theorem cell22_2339249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2339249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339249 prefixEnd_2339249 := by exact prefixLift 2339249
  have htrace : WordTrace (prefixWord ++ tailWord_2339249) baseStart_2339249 baseEnd_2339249 := by
    simpa [prefixWord, tailWord_2339249, baseEnd_2339249] using wordTrace_append hprefix tailTrace_2339249
  have hstable : (prefixWord ++ tailWord_2339249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339249).length < 2 ^ (prefixWord ++ tailWord_2339249).sum := by decide
  have hdescent : baseEnd_2339249 < baseStart_2339249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339253 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 6]
def baseStart_2339253 : Nat := 118140960795 + 2339253 * 2 ^ 59
def prefixEnd_2339253 : Nat := 4983230072969 + 3 ^ 40 * 2339253 * 2
def baseEnd_2339253 : Nat := 266924702549342532350995

theorem tailTrace_2339253 : CollatzResearch.WordTrace tailWord_2339253 prefixEnd_2339253 266924702549342532350995 := by
  unfold tailWord_2339253
  simp only [CollatzResearch.WordTrace]
  refine ⟨85319566194293368450686413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56879710796195578967124275 85319566194293368450686413)
  ·
    refine ⟨31994837322860013169007405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85319566194293368450686413 31994837322860013169007405)
    ·
      refine ⟨11998063996072504938377777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31994837322860013169007405 11998063996072504938377777)
      ·
        refine ⟨8998547997054378703783333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11998063996072504938377777 8998547997054378703783333)
        ·
          refine ⟨1687227749447696006959375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8998547997054378703783333 1687227749447696006959375)
          ·
            refine ⟨2530841624171544010439063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687227749447696006959375 2530841624171544010439063)
            ·
              refine ⟨3796262436257316015658595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530841624171544010439063 3796262436257316015658595)
              ·
                refine ⟨5694393654385974023487893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796262436257316015658595 5694393654385974023487893)
                ·
                  refine ⟨266924702549342532350995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5694393654385974023487893 266924702549342532350995)
                  ·
                    rfl

theorem cell22_2339253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_2339253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339253 prefixEnd_2339253 := by exact prefixLift 2339253
  have htrace : WordTrace (prefixWord ++ tailWord_2339253) baseStart_2339253 baseEnd_2339253 := by
    simpa [prefixWord, tailWord_2339253, baseEnd_2339253] using wordTrace_append hprefix tailTrace_2339253
  have hstable : (prefixWord ++ tailWord_2339253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339253).length < 2 ^ (prefixWord ++ tailWord_2339253).sum := by decide
  have hdescent : baseEnd_2339253 < baseStart_2339253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339279 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 5, 3]
def baseStart_2339279 : Nat := 118140960795 + 2339279 * 2 ^ 59
def prefixEnd_2339279 : Nat := 4983230072969 + 3 ^ 40 * 2339279 * 2
def baseEnd_2339279 : Nat := 800783007979372195902905

theorem tailTrace_2339279 : CollatzResearch.WordTrace tailWord_2339279 prefixEnd_2339279 800783007979372195902905 := by
  unfold tailWord_2339279
  simp only [CollatzResearch.WordTrace]
  refine ⟨85320514492199174891132891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56880342994799449927421927 85320514492199174891132891)
  ·
    refine ⟨127980771738298762336699337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85320514492199174891132891 127980771738298762336699337)
    ·
      refine ⟨95985578803724071752524503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127980771738298762336699337 95985578803724071752524503)
      ·
        refine ⟨143978368205586107628786755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95985578803724071752524503 143978368205586107628786755)
        ·
          refine ⟨215967552308379161443180133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143978368205586107628786755 215967552308379161443180133)
          ·
            refine ⟨40493916057821092770596275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215967552308379161443180133 40493916057821092770596275)
            ·
              refine ⟨60740874086731639155894413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40493916057821092770596275 60740874086731639155894413)
              ·
                refine ⟨22777827782524364683460405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60740874086731639155894413 22777827782524364683460405)
                ·
                  refine ⟨2135421354611659189074413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22777827782524364683460405 2135421354611659189074413)
                  ·
                    refine ⟨800783007979372195902905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135421354611659189074413 800783007979372195902905)
                    ·
                      rfl

theorem cell22_2339279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_2339279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339279 prefixEnd_2339279 := by exact prefixLift 2339279
  have htrace : WordTrace (prefixWord ++ tailWord_2339279) baseStart_2339279 baseEnd_2339279 := by
    simpa [prefixWord, tailWord_2339279, baseEnd_2339279] using wordTrace_append hprefix tailTrace_2339279
  have hstable : (prefixWord ++ tailWord_2339279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339279).length < 2 ^ (prefixWord ++ tailWord_2339279).sum := by decide
  have hdescent : baseEnd_2339279 < baseStart_2339279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339298 : List Nat := [3, 3, 3, 2, 2, 9]
def baseStart_2339298 : Nat := 118140960795 + 2339298 * 2 ^ 59
def prefixEnd_2339298 : Nat := 4983230072969 + 3 ^ 40 * 2339298 * 2
def baseEnd_2339298 : Nat := 9886290272440277526887

theorem tailTrace_2339298 : CollatzResearch.WordTrace tailWord_2339298 prefixEnd_2339298 9886290272440277526887 := by
  unfold tailWord_2339298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21330301869782585284018637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56880804986086894090716365 21330301869782585284018637)
  ·
    refine ⟨7998863201168469481506989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21330301869782585284018637 7998863201168469481506989)
    ·
      refine ⟨2999573700438176055565121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7998863201168469481506989 2999573700438176055565121)
      ·
        refine ⟨2249680275328632041673841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999573700438176055565121 2249680275328632041673841)
        ·
          refine ⟨1687260206496474031255381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2249680275328632041673841 1687260206496474031255381)
          ·
            refine ⟨9886290272440277526887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1687260206496474031255381 9886290272440277526887)
            ·
              rfl

theorem cell22_2339298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 9].length) (baseStart_2339298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339298 prefixEnd_2339298 := by exact prefixLift 2339298
  have htrace : WordTrace (prefixWord ++ tailWord_2339298) baseStart_2339298 baseEnd_2339298 := by
    simpa [prefixWord, tailWord_2339298, baseEnd_2339298] using wordTrace_append hprefix tailTrace_2339298
  have hstable : (prefixWord ++ tailWord_2339298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339298).length < 2 ^ (prefixWord ++ tailWord_2339298).sum := by decide
  have hdescent : baseEnd_2339298 < baseStart_2339298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339313 : List Nat := [1, 2, 2, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2339313 : Nat := 118140960795 + 2339313 * 2 ^ 59
def prefixEnd_2339313 : Nat := 4983230072969 + 3 ^ 40 * 2339313 * 2
def baseEnd_2339313 : Nat := 800794646874207440552801

theorem tailTrace_2339313 : CollatzResearch.WordTrace tailWord_2339313 prefixEnd_2339313 800794646874207440552801 := by
  unfold tailWord_2339313
  simp only [CollatzResearch.WordTrace]
  refine ⟨85321754574075998697870593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56881169716050665798580395 85321754574075998697870593)
  ·
    refine ⟨63991315930556999023402945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85321754574075998697870593 63991315930556999023402945)
    ·
      refine ⟨47993486947917749267552209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63991315930556999023402945 47993486947917749267552209)
      ·
        refine ⟨35995115210938311950664157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47993486947917749267552209 35995115210938311950664157)
        ·
          refine ⟨13498168204101866981499059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35995115210938311950664157 13498168204101866981499059)
          ·
            refine ⟨20247252306152800472248589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13498168204101866981499059 20247252306152800472248589)
            ·
              refine ⟨7592719614807300177093221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20247252306152800472248589 7592719614807300177093221)
              ·
                refine ⟨1423634927776368783204979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7592719614807300177093221 1423634927776368783204979)
                ·
                  refine ⟨2135452391664553174807469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1423634927776368783204979 2135452391664553174807469)
                  ·
                    refine ⟨800794646874207440552801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135452391664553174807469 800794646874207440552801)
                    ·
                      rfl

theorem cell22_2339313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2339313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339313 prefixEnd_2339313 := by exact prefixLift 2339313
  have htrace : WordTrace (prefixWord ++ tailWord_2339313) baseStart_2339313 baseEnd_2339313 := by
    simpa [prefixWord, tailWord_2339313, baseEnd_2339313] using wordTrace_append hprefix tailTrace_2339313
  have hstable : (prefixWord ++ tailWord_2339313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339313).length < 2 ^ (prefixWord ++ tailWord_2339313).sum := by decide
  have hdescent : baseEnd_2339313 < baseStart_2339313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339330 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2339330 : Nat := 118140960795 + 2339330 * 2 ^ 59
def prefixEnd_2339330 : Nat := 4983230072969 + 3 ^ 40 * 2339330 * 2
def baseEnd_2339330 : Nat := 800800466321625062877749

theorem tailTrace_2339330 : CollatzResearch.WordTrace tailWord_2339330 prefixEnd_2339330 800800466321625062877749 := by
  unfold tailWord_2339330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21330593653753602650309861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56881583076676273734159629 21330593653753602650309861)
  ·
    refine ⟨3999486310078800496933099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21330593653753602650309861 3999486310078800496933099)
    ·
      refine ⟨5999229465118200745399649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3999486310078800496933099 5999229465118200745399649)
      ·
        refine ⟨4499422098838650559049737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5999229465118200745399649 4499422098838650559049737)
        ·
          refine ⟨3374566574128987919287303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499422098838650559049737 3374566574128987919287303)
          ·
            refine ⟨5061849861193481878930955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374566574128987919287303 5061849861193481878930955)
            ·
              refine ⟨7592774791790222818396433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5061849861193481878930955 7592774791790222818396433)
              ·
                refine ⟨5694581093842667113797325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7592774791790222818396433 5694581093842667113797325)
                ·
                  refine ⟨2135467910191000167673997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5694581093842667113797325 2135467910191000167673997)
                  ·
                    refine ⟨800800466321625062877749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135467910191000167673997 800800466321625062877749)
                    ·
                      rfl

theorem cell22_2339330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2339330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339330 prefixEnd_2339330 := by exact prefixLift 2339330
  have htrace : WordTrace (prefixWord ++ tailWord_2339330) baseStart_2339330 baseEnd_2339330 := by
    simpa [prefixWord, tailWord_2339330, baseEnd_2339330] using wordTrace_append hprefix tailTrace_2339330
  have hstable : (prefixWord ++ tailWord_2339330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339330).length < 2 ^ (prefixWord ++ tailWord_2339330).sum := by decide
  have hdescent : baseEnd_2339330 < baseStart_2339330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339360 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_2339360 : Nat := 118140960795 + 2339360 * 2 ^ 59
def prefixEnd_2339360 : Nat := 4983230072969 + 3 ^ 40 * 2339360 * 2
def baseEnd_2339360 : Nat := 266936911978238328209219

theorem tailTrace_2339360 : CollatzResearch.WordTrace tailWord_2339360 prefixEnd_2339360 266936911978238328209219 := by
  unfold tailWord_2339360
  simp only [CollatzResearch.WordTrace]
  refine ⟨42661734402452862862415767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56882312536603817149887689 42661734402452862862415767)
  ·
    refine ⟨63992601603679294293623651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42661734402452862862415767 63992601603679294293623651)
    ·
      refine ⟨95988902405518941440435477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63992601603679294293623651 95988902405518941440435477)
      ·
        refine ⟨4499479800258700380020413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95988902405518941440435477 4499479800258700380020413)
        ·
          refine ⟨1687304925097012642507655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4499479800258700380020413 1687304925097012642507655)
          ·
            refine ⟨2530957387645518963761483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687304925097012642507655 2530957387645518963761483)
            ·
              refine ⟨3796436081468278445642225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530957387645518963761483 3796436081468278445642225)
              ·
                refine ⟨2847327061101208834231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3796436081468278445642225 2847327061101208834231669)
                ·
                  refine ⟨266936911978238328209219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2847327061101208834231669 266936911978238328209219)
                  ·
                    rfl

theorem cell22_2339360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_2339360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339360 prefixEnd_2339360 := by exact prefixLift 2339360
  have htrace : WordTrace (prefixWord ++ tailWord_2339360) baseStart_2339360 baseEnd_2339360 := by
    simpa [prefixWord, tailWord_2339360, baseEnd_2339360] using wordTrace_append hprefix tailTrace_2339360
  have hstable : (prefixWord ++ tailWord_2339360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339360).length < 2 ^ (prefixWord ++ tailWord_2339360).sum := by decide
  have hdescent : baseEnd_2339360 < baseStart_2339360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339384 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2339384 : Nat := 118140960795 + 2339384 * 2 ^ 59
def prefixEnd_2339384 : Nat := 4983230072969 + 3 ^ 40 * 2339384 * 2
def baseEnd_2339384 : Nat := 800818951625186922027583

theorem tailTrace_2339384 : CollatzResearch.WordTrace tailWord_2339384 prefixEnd_2339384 800818951625186922027583 := by
  unfold tailWord_2339384
  simp only [CollatzResearch.WordTrace]
  refine ⟨42662172078409388911852603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56882896104545851882470137 42662172078409388911852603)
  ·
    refine ⟨63993258117614083367778905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42662172078409388911852603 63993258117614083367778905)
    ·
      refine ⟨47994943588210562525834179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63993258117614083367778905 47994943588210562525834179)
      ·
        refine ⟨71992415382315843788751269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47994943588210562525834179 71992415382315843788751269)
        ·
          refine ⟨13498577884184220710390863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71992415382315843788751269 13498577884184220710390863)
          ·
            refine ⟨20247866826276331065586295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13498577884184220710390863 20247866826276331065586295)
            ·
              refine ⟨30371800239414496598379443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20247866826276331065586295 30371800239414496598379443)
              ·
                refine ⟨45557700359121744897569165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30371800239414496598379443 45557700359121744897569165)
                ·
                  refine ⟨17084137634670654336588437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45557700359121744897569165 17084137634670654336588437)
                  ·
                    refine ⟨800818951625186922027583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17084137634670654336588437 800818951625186922027583)
                    ·
                      rfl

theorem cell22_2339384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2339384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339384 prefixEnd_2339384 := by exact prefixLift 2339384
  have htrace : WordTrace (prefixWord ++ tailWord_2339384) baseStart_2339384 baseEnd_2339384 := by
    simpa [prefixWord, tailWord_2339384, baseEnd_2339384] using wordTrace_append hprefix tailTrace_2339384
  have hstable : (prefixWord ++ tailWord_2339384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339384).length < 2 ^ (prefixWord ++ tailWord_2339384).sum := by decide
  have hdescent : baseEnd_2339384 < baseStart_2339384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339386 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_2339386 : Nat := 118140960795 + 2339386 * 2 ^ 59
def prefixEnd_2339386 : Nat := 4983230072969 + 3 ^ 40 * 2339386 * 2
def baseEnd_2339386 : Nat := 800819636266059583477577

theorem tailTrace_2339386 : CollatzResearch.WordTrace tailWord_2339386 prefixEnd_2339386 800819636266059583477577 := by
  unfold tailWord_2339386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21331104275702883041319503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56882944735207688110185341 21331104275702883041319503)
  ·
    refine ⟨31996656413554324561979255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21331104275702883041319503 31996656413554324561979255)
    ·
      refine ⟨47994984620331486842968883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31996656413554324561979255 47994984620331486842968883)
      ·
        refine ⟨71992476930497230264453325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47994984620331486842968883 71992476930497230264453325)
        ·
          refine ⟨26997178848936461349169997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71992476930497230264453325 26997178848936461349169997)
          ·
            refine ⟨10123942068351173005938749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26997178848936461349169997 10123942068351173005938749)
            ·
              refine ⟨3796478275631689877227031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10123942068351173005938749 3796478275631689877227031)
              ·
                refine ⟨5694717413447534815840547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796478275631689877227031 5694717413447534815840547)
                ·
                  refine ⟨8542076120171302223760821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5694717413447534815840547 8542076120171302223760821)
                  ·
                    refine ⟨800819636266059583477577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542076120171302223760821 800819636266059583477577)
                    ·
                      rfl

theorem cell22_2339386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_2339386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339386 prefixEnd_2339386 := by exact prefixLift 2339386
  have htrace : WordTrace (prefixWord ++ tailWord_2339386) baseStart_2339386 baseEnd_2339386 := by
    simpa [prefixWord, tailWord_2339386, baseEnd_2339386] using wordTrace_append hprefix tailTrace_2339386
  have hstable : (prefixWord ++ tailWord_2339386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339386).length < 2 ^ (prefixWord ++ tailWord_2339386).sum := by decide
  have hdescent : baseEnd_2339386 < baseStart_2339386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339405 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2339405 : Nat := 118140960795 + 2339405 * 2 ^ 59
def prefixEnd_2339405 : Nat := 4983230072969 + 3 ^ 40 * 2339405 * 2
def baseEnd_2339405 : Nat := 266942046784783289084173

theorem tailTrace_2339405 : CollatzResearch.WordTrace tailWord_2339405 prefixEnd_2339405 266942046784783289084173 := by
  unfold tailWord_2339405
  simp only [CollatzResearch.WordTrace]
  refine ⟨85325110089742698410219669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56883406726495132273479779 85325110089742698410219669)
  ·
    refine ⟨3999614535456688987979047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85325110089742698410219669 3999614535456688987979047)
    ·
      refine ⟨5999421803185033481968571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3999614535456688987979047 5999421803185033481968571)
      ·
        refine ⟨8999132704777550222952857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999421803185033481968571 8999132704777550222952857)
        ·
          refine ⟨6749349528583162667214643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8999132704777550222952857 6749349528583162667214643)
          ·
            refine ⟨10124024292874744000821965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6749349528583162667214643 10124024292874744000821965)
            ·
              refine ⟨3796509109828029000308237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10124024292874744000821965 3796509109828029000308237)
              ·
                refine ⟨1423690916185510875115589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3796509109828029000308237 1423690916185510875115589)
                ·
                  refine ⟨266942046784783289084173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1423690916185510875115589 266942046784783289084173)
                  ·
                    rfl

theorem cell22_2339405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2339405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339405 prefixEnd_2339405 := by exact prefixLift 2339405
  have htrace : WordTrace (prefixWord ++ tailWord_2339405) baseStart_2339405 baseEnd_2339405 := by
    simpa [prefixWord, tailWord_2339405, baseEnd_2339405] using wordTrace_append hprefix tailTrace_2339405
  have hstable : (prefixWord ++ tailWord_2339405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339405).length < 2 ^ (prefixWord ++ tailWord_2339405).sum := by decide
  have hdescent : baseEnd_2339405 < baseStart_2339405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339437 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2339437 : Nat := 118140960795 + 2339437 * 2 ^ 59
def prefixEnd_2339437 : Nat := 4983230072969 + 3 ^ 40 * 2339437 * 2
def baseEnd_2339437 : Nat := 800837094608312450452421

theorem tailTrace_2339437 : CollatzResearch.WordTrace tailWord_2339437 prefixEnd_2339437 800837094608312450452421 := by
  unfold tailWord_2339437
  simp only [CollatzResearch.WordTrace]
  refine ⟨85326277225626767875384565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56884184817084511916923043 85326277225626767875384565)
  ·
    refine ⟨7999338489902509488317303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85326277225626767875384565 7999338489902509488317303)
    ·
      refine ⟨11999007734853764232475955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999338489902509488317303 11999007734853764232475955)
      ·
        refine ⟨17998511602280646348713933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11999007734853764232475955 17998511602280646348713933)
        ·
          refine ⟨6749441850855242380767725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17998511602280646348713933 6749441850855242380767725)
          ·
            refine ⟨2531040694070715892787897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6749441850855242380767725 2531040694070715892787897)
            ·
              refine ⟨1898280520553036919590923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2531040694070715892787897 1898280520553036919590923)
              ·
                refine ⟨2847420780829555379386385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1898280520553036919590923 2847420780829555379386385)
                ·
                  refine ⟨2135565585622166534539789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2847420780829555379386385 2135565585622166534539789)
                  ·
                    refine ⟨800837094608312450452421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135565585622166534539789 800837094608312450452421)
                    ·
                      rfl

theorem cell22_2339437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2339437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339437 prefixEnd_2339437 := by exact prefixLift 2339437
  have htrace : WordTrace (prefixWord ++ tailWord_2339437) baseStart_2339437 baseEnd_2339437 := by
    simpa [prefixWord, tailWord_2339437, baseEnd_2339437] using wordTrace_append hprefix tailTrace_2339437
  have hstable : (prefixWord ++ tailWord_2339437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339437).length < 2 ^ (prefixWord ++ tailWord_2339437).sum := by decide
  have hdescent : baseEnd_2339437 < baseStart_2339437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339540 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_2339540 : Nat := 118140960795 + 2339540 * 2 ^ 59
def prefixEnd_2339540 : Nat := 4983230072969 + 3 ^ 40 * 2339540 * 2
def baseEnd_2339540 : Nat := 266957451204418171709035

theorem tailTrace_2339540 : CollatzResearch.WordTrace tailWord_2339540 prefixEnd_2339540 266957451204418171709035 := by
  unfold tailWord_2339540
  simp only [CollatzResearch.WordTrace]
  refine ⟨42665016972126808233192037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56886689296169077644256049 42665016972126808233192037)
  ·
    refine ⟨7999690682273776543723507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42665016972126808233192037 7999690682273776543723507)
    ·
      refine ⟨11999536023410664815585261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7999690682273776543723507 11999536023410664815585261)
      ·
        refine ⟨4499826008778999305844473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11999536023410664815585261 4499826008778999305844473)
        ·
          refine ⟨3374869506584249479383355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4499826008778999305844473 3374869506584249479383355)
          ·
            refine ⟨5062304259876374219075033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374869506584249479383355 5062304259876374219075033)
            ·
              refine ⟨3796728194907280664306275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5062304259876374219075033 3796728194907280664306275)
              ·
                refine ⟨5695092292360920996459413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796728194907280664306275 5695092292360920996459413)
                ·
                  refine ⟨266957451204418171709035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5695092292360920996459413 266957451204418171709035)
                  ·
                    rfl

theorem cell22_2339540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_2339540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339540 prefixEnd_2339540 := by exact prefixLift 2339540
  have htrace : WordTrace (prefixWord ++ tailWord_2339540) baseStart_2339540 baseEnd_2339540 := by
    simpa [prefixWord, tailWord_2339540, baseEnd_2339540] using wordTrace_append hprefix tailTrace_2339540
  have hstable : (prefixWord ++ tailWord_2339540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339540).length < 2 ^ (prefixWord ++ tailWord_2339540).sum := by decide
  have hdescent : baseEnd_2339540 < baseStart_2339540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339555 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 5]
def baseStart_2339555 : Nat := 118140960795 + 2339555 * 2 ^ 59
def prefixEnd_2339555 : Nat := 4983230072969 + 3 ^ 40 * 2339555 * 2
def baseEnd_2339555 : Nat := 800877488419799476002059

theorem tailTrace_2339555 : CollatzResearch.WordTrace tailWord_2339555 prefixEnd_2339555 800877488419799476002059 := by
  unfold tailWord_2339555
  simp only [CollatzResearch.WordTrace]
  refine ⟨85330581039199274028180119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56887054026132849352120079 85330581039199274028180119)
  ·
    refine ⟨127995871558798911042270179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85330581039199274028180119 127995871558798911042270179)
    ·
      refine ⟨191993807338198366563405269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127995871558798911042270179 191993807338198366563405269)
      ·
        refine ⟨4499854859489024216329811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 191993807338198366563405269 4499854859489024216329811)
        ·
          refine ⟨6749782289233536324494717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499854859489024216329811 6749782289233536324494717)
          ·
            refine ⟨2531168358462576121685519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6749782289233536324494717 2531168358462576121685519)
            ·
              refine ⟨3796752537693864182528279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531168358462576121685519 3796752537693864182528279)
              ·
                refine ⟨5695128806540796273792419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3796752537693864182528279 5695128806540796273792419)
                ·
                  refine ⟨8542693209811194410688629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695128806540796273792419 8542693209811194410688629)
                  ·
                    refine ⟨800877488419799476002059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8542693209811194410688629 800877488419799476002059)
                    ·
                      rfl

theorem cell22_2339555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 5].length) (baseStart_2339555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339555 prefixEnd_2339555 := by exact prefixLift 2339555
  have htrace : WordTrace (prefixWord ++ tailWord_2339555) baseStart_2339555 baseEnd_2339555 := by
    simpa [prefixWord, tailWord_2339555, baseEnd_2339555] using wordTrace_append hprefix tailTrace_2339555
  have hstable : (prefixWord ++ tailWord_2339555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339555).length < 2 ^ (prefixWord ++ tailWord_2339555).sum := by decide
  have hdescent : baseEnd_2339555 < baseStart_2339555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339673 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_2339673 : Nat := 118140960795 + 2339673 * 2 ^ 59
def prefixEnd_2339673 : Nat := 4983230072969 + 3 ^ 40 * 2339673 * 2
def baseEnd_2339673 : Nat := 800917882231286501551697

theorem tailTrace_2339673 : CollatzResearch.WordTrace tailWord_2339673 prefixEnd_2339673 800917882231286501551697 := by
  unfold tailWord_2339673
  simp only [CollatzResearch.WordTrace]
  refine ⟨85334884852771780180975673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56889923235181186787317115 85334884852771780180975673)
  ·
    refine ⟨64001163639578835135731755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85334884852771780180975673 64001163639578835135731755)
    ·
      refine ⟨96001745459368252703597633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64001163639578835135731755 96001745459368252703597633)
      ·
        refine ⟨72001309094526189527698225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96001745459368252703597633 72001309094526189527698225)
        ·
          refine ⟨54000981820894642145773669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72001309094526189527698225 54000981820894642145773669)
          ·
            refine ⟨10125184091417745402332563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54000981820894642145773669 10125184091417745402332563)
            ·
              refine ⟨15187776137126618103498845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10125184091417745402332563 15187776137126618103498845)
              ·
                refine ⟨5695416051422481788812067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15187776137126618103498845 5695416051422481788812067)
                ·
                  refine ⟨8543124077133722683218101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5695416051422481788812067 8543124077133722683218101)
                  ·
                    refine ⟨800917882231286501551697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8543124077133722683218101 800917882231286501551697)
                    ·
                      rfl

theorem cell22_2339673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_2339673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339673 prefixEnd_2339673 := by exact prefixLift 2339673
  have htrace : WordTrace (prefixWord ++ tailWord_2339673) baseStart_2339673 baseEnd_2339673 := by
    simpa [prefixWord, tailWord_2339673, baseEnd_2339673] using wordTrace_append hprefix tailTrace_2339673
  have hstable : (prefixWord ++ tailWord_2339673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339673).length < 2 ^ (prefixWord ++ tailWord_2339673).sum := by decide
  have hdescent : baseEnd_2339673 < baseStart_2339673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339735 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 3, 3]
def baseStart_2339735 : Nat := 118140960795 + 2339735 * 2 ^ 59
def prefixEnd_2339735 : Nat := 4983230072969 + 3 ^ 40 * 2339735 * 2
def baseEnd_2339735 : Nat := 800939106098339006501507

theorem tailTrace_2339735 : CollatzResearch.WordTrace tailWord_2339735 prefixEnd_2339735 800939106098339006501507 := by
  unfold tailWord_2339735
  simp only [CollatzResearch.WordTrace]
  refine ⟨85337146178547164769732659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56891430785698109846488439 85337146178547164769732659)
  ·
    refine ⟨128005719267820747154598989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85337146178547164769732659 128005719267820747154598989)
    ·
      refine ⟨48002144725432780182974621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128005719267820747154598989 48002144725432780182974621)
      ·
        refine ⟨18000804272037292568615483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48002144725432780182974621 18000804272037292568615483)
        ·
          refine ⟨27001206408055938852923225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18000804272037292568615483 27001206408055938852923225)
          ·
            refine ⟨20250904806041954139692419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27001206408055938852923225 20250904806041954139692419)
            ·
              refine ⟨30376357209062931209538629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20250904806041954139692419 30376357209062931209538629)
              ·
                refine ⟨5695566976699299601788493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30376357209062931209538629 5695566976699299601788493)
                ·
                  refine ⟨2135837616262237350670685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5695566976699299601788493 2135837616262237350670685)
                  ·
                    refine ⟨800939106098339006501507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135837616262237350670685 800939106098339006501507)
                    ·
                      rfl

theorem cell22_2339735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_2339735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339735 prefixEnd_2339735 := by exact prefixLift 2339735
  have htrace : WordTrace (prefixWord ++ tailWord_2339735) baseStart_2339735 baseEnd_2339735 := by
    simpa [prefixWord, tailWord_2339735, baseEnd_2339735] using wordTrace_append hprefix tailTrace_2339735
  have hstable : (prefixWord ++ tailWord_2339735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339735).length < 2 ^ (prefixWord ++ tailWord_2339735).sum := by decide
  have hdescent : baseEnd_2339735 < baseStart_2339735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339748 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2339748 : Nat := 118140960795 + 2339748 * 2 ^ 59
def prefixEnd_2339748 : Nat := 4983230072969 + 3 ^ 40 * 2339748 * 2
def baseEnd_2339748 : Nat := 266981185421337101975489

theorem tailTrace_2339748 : CollatzResearch.WordTrace tailWord_2339748 prefixEnd_2339748 266981185421337101975489 := by
  unfold tailWord_2339748
  simp only [CollatzResearch.WordTrace]
  refine ⟨42668810163750033994977949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56891746885000045326637265 42668810163750033994977949)
  ·
    refine ⟨16000803811406262748116731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42668810163750033994977949 16000803811406262748116731)
    ·
      refine ⟨24001205717109394122175097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16000803811406262748116731 24001205717109394122175097)
      ·
        refine ⟨18000904287832045591631323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24001205717109394122175097 18000904287832045591631323)
        ·
          refine ⟨27001356431748068387446985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18000904287832045591631323 27001356431748068387446985)
          ·
            refine ⟨20251017323811051290585239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27001356431748068387446985 20251017323811051290585239)
            ·
              refine ⟨30376525985716576935877859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20251017323811051290585239 30376525985716576935877859)
              ·
                refine ⟨45564788978574865403816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30376525985716576935877859 45564788978574865403816789)
                ·
                  refine ⟨266981185421337101975489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45564788978574865403816789 266981185421337101975489)
                  ·
                    rfl

theorem cell22_2339748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2339748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339748 prefixEnd_2339748 := by exact prefixLift 2339748
  have htrace : WordTrace (prefixWord ++ tailWord_2339748) baseStart_2339748 baseEnd_2339748 := by
    simpa [prefixWord, tailWord_2339748, baseEnd_2339748] using wordTrace_append hprefix tailTrace_2339748
  have hstable : (prefixWord ++ tailWord_2339748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339748).length < 2 ^ (prefixWord ++ tailWord_2339748).sum := by decide
  have hdescent : baseEnd_2339748 < baseStart_2339748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_2339763 : Nat := 118140960795 + 2339763 * 2 ^ 59
def prefixEnd_2339763 : Nat := 4983230072969 + 3 ^ 40 * 2339763 * 2
def baseEnd_2339763 : Nat := 800948691070556266801421

theorem tailTrace_2339763 : CollatzResearch.WordTrace tailWord_2339763 prefixEnd_2339763 800948691070556266801421 := by
  unfold tailWord_2339763
  simp only [CollatzResearch.WordTrace]
  refine ⟨85338167422445725551751943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56892111614963817034501295 85338167422445725551751943)
  ·
    refine ⟨128007251133668588327627915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85338167422445725551751943 128007251133668588327627915)
    ·
      refine ⟨192010876700502882491441873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128007251133668588327627915 192010876700502882491441873)
      ·
        refine ⟨144008157525377161868581405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192010876700502882491441873 144008157525377161868581405)
        ·
          refine ⟨54003059072016435700718027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144008157525377161868581405 54003059072016435700718027)
          ·
            refine ⟨81004588608024653551077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54003059072016435700718027 81004588608024653551077041)
            ·
              refine ⟨60753441456018490163307781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81004588608024653551077041 60753441456018490163307781)
              ·
                refine ⟨11391270273003466905620209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60753441456018490163307781 11391270273003466905620209)
                ·
                  refine ⟨8543452704752600179215157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11391270273003466905620209 8543452704752600179215157)
                  ·
                    refine ⟨800948691070556266801421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8543452704752600179215157 800948691070556266801421)
                    ·
                      rfl

theorem cell22_2339763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_2339763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339763 prefixEnd_2339763 := by exact prefixLift 2339763
  have htrace : WordTrace (prefixWord ++ tailWord_2339763) baseStart_2339763 baseEnd_2339763 := by
    simpa [prefixWord, tailWord_2339763, baseEnd_2339763] using wordTrace_append hprefix tailTrace_2339763
  have hstable : (prefixWord ++ tailWord_2339763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339763).length < 2 ^ (prefixWord ++ tailWord_2339763).sum := by decide
  have hdescent : baseEnd_2339763 < baseStart_2339763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339765 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 5]
def baseStart_2339765 : Nat := 118140960795 + 2339765 * 2 ^ 59
def prefixEnd_2339765 : Nat := 4983230072969 + 3 ^ 40 * 2339765 * 2
def baseEnd_2339765 : Nat := 266983125237142976083805

theorem tailTrace_2339765 : CollatzResearch.WordTrace tailWord_2339765 prefixEnd_2339765 266983125237142976083805 := by
  unfold tailWord_2339765
  simp only [CollatzResearch.WordTrace]
  refine ⟨85338240368438479893324749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56892160245625653262216499 85338240368438479893324749)
  ·
    refine ⟨32001840138164429959996781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85338240368438479893324749 32001840138164429959996781)
    ·
      refine ⟨12000690051811661234998793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32001840138164429959996781 12000690051811661234998793)
      ·
        refine ⟨9000517538858745926249095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12000690051811661234998793 9000517538858745926249095)
        ·
          refine ⟨13500776308288118889373643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9000517538858745926249095 13500776308288118889373643)
          ·
            refine ⟨20251164462432178334060465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13500776308288118889373643 20251164462432178334060465)
            ·
              refine ⟨15188373346824133750545349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20251164462432178334060465 15188373346824133750545349)
              ·
                refine ⟨2847820002529525078227253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15188373346824133750545349 2847820002529525078227253)
                ·
                  refine ⟨266983125237142976083805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2847820002529525078227253 266983125237142976083805)
                  ·
                    rfl

theorem cell22_2339765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_2339765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339765 prefixEnd_2339765 := by exact prefixLift 2339765
  have htrace : WordTrace (prefixWord ++ tailWord_2339765) baseStart_2339765 baseEnd_2339765 := by
    simpa [prefixWord, tailWord_2339765, baseEnd_2339765] using wordTrace_append hprefix tailTrace_2339765
  have hstable : (prefixWord ++ tailWord_2339765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339765).length < 2 ^ (prefixWord ++ tailWord_2339765).sum := by decide
  have hdescent : baseEnd_2339765 < baseStart_2339765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339793 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 8]
def baseStart_2339793 : Nat := 118140960795 + 2339793 * 2 ^ 59
def prefixEnd_2339793 : Nat := 4983230072969 + 3 ^ 40 * 2339793 * 2
def baseEnd_2339793 : Nat := 266986320227882062850443

theorem tailTrace_2339793 : CollatzResearch.WordTrace tailWord_2339793 prefixEnd_2339793 266986320227882062850443 := by
  unfold tailWord_2339793
  simp only [CollatzResearch.WordTrace]
  refine ⟨85339261612337040675344033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56892841074891360450229355 85339261612337040675344033)
  ·
    refine ⟨64004446209252780506508025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85339261612337040675344033 64004446209252780506508025)
    ·
      refine ⟨48003334656939585379881019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64004446209252780506508025 48003334656939585379881019)
      ·
        refine ⟨72005001985409378069821529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48003334656939585379881019 72005001985409378069821529)
        ·
          refine ⟨54003751489057033552366147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72005001985409378069821529 54003751489057033552366147)
          ·
            refine ⟨81005627233585550328549221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54003751489057033552366147 81005627233585550328549221)
            ·
              refine ⟨15188555106297290686602979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81005627233585550328549221 15188555106297290686602979)
              ·
                refine ⟨22782832659445936029904469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15188555106297290686602979 22782832659445936029904469)
                ·
                  refine ⟨266986320227882062850443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22782832659445936029904469 266986320227882062850443)
                  ·
                    rfl

theorem cell22_2339793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_2339793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339793 prefixEnd_2339793 := by exact prefixLift 2339793
  have htrace : WordTrace (prefixWord ++ tailWord_2339793) baseStart_2339793 baseEnd_2339793 := by
    simpa [prefixWord, tailWord_2339793, baseEnd_2339793] using wordTrace_append hprefix tailTrace_2339793
  have hstable : (prefixWord ++ tailWord_2339793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339793).length < 2 ^ (prefixWord ++ tailWord_2339793).sum := by decide
  have hdescent : baseEnd_2339793 < baseStart_2339793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339872 : List Nat := [2, 1, 1, 7, 1, 1, 9]
def baseStart_2339872 : Nat := 118140960795 + 2339872 * 2 ^ 59
def prefixEnd_2339872 : Nat := 4983230072969 + 3 ^ 40 * 2339872 * 2
def baseEnd_2339872 : Nat := 29666148296226530215781

theorem tailTrace_2339872 : CollatzResearch.WordTrace tailWord_2339872 prefixEnd_2339872 29666148296226530215781 := by
  unfold tailWord_2339872
  simp only [CollatzResearch.WordTrace]
  refine ⟨42671071489525418583734935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56894761986033891444979913 42671071489525418583734935)
  ·
    refine ⟨64006607234288127875602403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42671071489525418583734935 64006607234288127875602403)
    ·
      refine ⟨96009910851432191813403605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64006607234288127875602403 96009910851432191813403605)
      ·
        refine ⟨2250232285580441995626647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 96009910851432191813403605 2250232285580441995626647)
        ·
          refine ⟨3375348428370662993439971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250232285580441995626647 3375348428370662993439971)
          ·
            refine ⟨5063022642555994490159957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375348428370662993439971 5063022642555994490159957)
            ·
              refine ⟨29666148296226530215781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5063022642555994490159957 29666148296226530215781)
              ·
                rfl

theorem cell22_2339872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 9].length) (baseStart_2339872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339872 prefixEnd_2339872 := by exact prefixLift 2339872
  have htrace : WordTrace (prefixWord ++ tailWord_2339872) baseStart_2339872 baseEnd_2339872 := by
    simpa [prefixWord, tailWord_2339872, baseEnd_2339872] using wordTrace_append hprefix tailTrace_2339872
  have hstable : (prefixWord ++ tailWord_2339872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339872).length < 2 ^ (prefixWord ++ tailWord_2339872).sum := by decide
  have hdescent : baseEnd_2339872 < baseStart_2339872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339876 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_2339876 : Nat := 118140960795 + 2339876 * 2 ^ 59
def prefixEnd_2339876 : Nat := 4983230072969 + 3 ^ 40 * 2339876 * 2
def baseEnd_2339876 : Nat := 800987373279861638726075

theorem tailTrace_2339876 : CollatzResearch.WordTrace tailWord_2339876 prefixEnd_2339876 800987373279861638726075 := by
  unfold tailWord_2339876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42671144435518172925307741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56894859247357563900410321 42671144435518172925307741)
  ·
    refine ⟨16001679163319314846990403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42671144435518172925307741 16001679163319314846990403)
    ·
      refine ⟨24002518744978972270485605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16001679163319314846990403 24002518744978972270485605)
      ·
        refine ⟨4500472264683557300716051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24002518744978972270485605 4500472264683557300716051)
        ·
          refine ⟨6750708397025335951074077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4500472264683557300716051 6750708397025335951074077)
          ·
            refine ⟨2531515648884500981652779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6750708397025335951074077 2531515648884500981652779)
            ·
              refine ⟨3797273473326751472479169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2531515648884500981652779 3797273473326751472479169)
              ·
                refine ⟨2847955104995063604359377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3797273473326751472479169 2847955104995063604359377)
                ·
                  refine ⟨2135966328746297703269533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2847955104995063604359377 2135966328746297703269533)
                  ·
                    refine ⟨800987373279861638726075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2135966328746297703269533 800987373279861638726075)
                    ·
                      rfl

theorem cell22_2339876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_2339876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339876 prefixEnd_2339876 := by exact prefixLift 2339876
  have htrace : WordTrace (prefixWord ++ tailWord_2339876) baseStart_2339876 baseEnd_2339876 := by
    simpa [prefixWord, tailWord_2339876, baseEnd_2339876] using wordTrace_append hprefix tailTrace_2339876
  have hstable : (prefixWord ++ tailWord_2339876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339876).length < 2 ^ (prefixWord ++ tailWord_2339876).sum := by decide
  have hdescent : baseEnd_2339876 < baseStart_2339876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339917 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2339917 : Nat := 118140960795 + 2339917 * 2 ^ 59
def prefixEnd_2339917 : Nat := 4983230072969 + 3 ^ 40 * 2339917 * 2
def baseEnd_2339917 : Nat := 267000469472583732816983

theorem tailTrace_2339917 : CollatzResearch.WordTrace tailWord_2339917 prefixEnd_2339917 267000469472583732816983 := by
  unfold tailWord_2339917
  simp only [CollatzResearch.WordTrace]
  refine ⟨85343784263887809852858005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56895856175925206568572003 85343784263887809852858005)
  ·
    refine ⟨4000489887369741086852719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85343784263887809852858005 4000489887369741086852719)
    ·
      refine ⟨6000734831054611630279079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4000489887369741086852719 6000734831054611630279079)
      ·
        refine ⟨9001102246581917445418619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6000734831054611630279079 9001102246581917445418619)
        ·
          refine ⟨13501653369872876168127929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001102246581917445418619 13501653369872876168127929)
          ·
            refine ⟨10126240027404657126095947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13501653369872876168127929 10126240027404657126095947)
            ·
              refine ⟨15189360041106985689143921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10126240027404657126095947 15189360041106985689143921)
              ·
                refine ⟨11392020030830239266857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15189360041106985689143921 11392020030830239266857941)
                ·
                  refine ⟨267000469472583732816983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11392020030830239266857941 267000469472583732816983)
                  ·
                    rfl

theorem cell22_2339917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2339917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339917 prefixEnd_2339917 := by exact prefixLift 2339917
  have htrace : WordTrace (prefixWord ++ tailWord_2339917) baseStart_2339917 baseEnd_2339917 := by
    simpa [prefixWord, tailWord_2339917, baseEnd_2339917] using wordTrace_append hprefix tailTrace_2339917
  have hstable : (prefixWord ++ tailWord_2339917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339917).length < 2 ^ (prefixWord ++ tailWord_2339917).sum := by decide
  have hdescent : baseEnd_2339917 < baseStart_2339917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339977 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_2339977 : Nat := 118140960795 + 2339977 * 2 ^ 59
def prefixEnd_2339977 : Nat := 4983230072969 + 3 ^ 40 * 2339977 * 2
def baseEnd_2339977 : Nat := 801021947643931041950765

theorem tailTrace_2339977 : CollatzResearch.WordTrace tailWord_2339977 prefixEnd_2339977 801021947643931041950765 := by
  unfold tailWord_2339977
  simp only [CollatzResearch.WordTrace]
  refine ⟨85345972643670440100042185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56897315095780293400028123 85345972643670440100042185)
  ·
    refine ⟨64009479482752830075031639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85345972643670440100042185 64009479482752830075031639)
    ·
      refine ⟨96014219224129245112547459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64009479482752830075031639 96014219224129245112547459)
      ·
        refine ⟨144021328836193867668821189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96014219224129245112547459 144021328836193867668821189)
        ·
          refine ⟨27003999156786350187903973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144021328836193867668821189 27003999156786350187903973)
          ·
            refine ⟨5063249841897440660231995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27003999156786350187903973 5063249841897440660231995)
            ·
              refine ⟨7594874762846160990347993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063249841897440660231995 7594874762846160990347993)
              ·
                refine ⟨5696156072134620742760995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7594874762846160990347993 5696156072134620742760995)
                ·
                  refine ⟨8544234108201931114141493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5696156072134620742760995 8544234108201931114141493)
                  ·
                    refine ⟨801021947643931041950765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8544234108201931114141493 801021947643931041950765)
                    ·
                      rfl

theorem cell22_2339977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_2339977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339977 prefixEnd_2339977 := by exact prefixLift 2339977
  have htrace : WordTrace (prefixWord ++ tailWord_2339977) baseStart_2339977 baseEnd_2339977 := by
    simpa [prefixWord, tailWord_2339977, baseEnd_2339977] using wordTrace_append hprefix tailTrace_2339977
  have hstable : (prefixWord ++ tailWord_2339977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339977).length < 2 ^ (prefixWord ++ tailWord_2339977).sum := by decide
  have hdescent : baseEnd_2339977 < baseStart_2339977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2339996 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_2339996 : Nat := 118140960795 + 2339996 * 2 ^ 59
def prefixEnd_2339996 : Nat := 4983230072969 + 3 ^ 40 * 2339996 * 2
def baseEnd_2339996 : Nat := 267009483910740441908569

theorem tailTrace_2339996 : CollatzResearch.WordTrace tailWord_2339996 prefixEnd_2339996 267009483910740441908569 := by
  unfold tailWord_2339996
  simp only [CollatzResearch.WordTrace]
  refine ⟨42673332815300803172491921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56897777087067737563322561 42673332815300803172491921)
  ·
    refine ⟨32004999611475602379368941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42673332815300803172491921 32004999611475602379368941)
    ·
      refine ⟨12001874854303350892263353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32004999611475602379368941 12001874854303350892263353)
      ·
        refine ⟨9001406140727513169197515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12001874854303350892263353 9001406140727513169197515)
        ·
          refine ⟨13502109211091269753796273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9001406140727513169197515 13502109211091269753796273)
          ·
            refine ⟨10126581908318452315347205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13502109211091269753796273 10126581908318452315347205)
            ·
              refine ⟨1898734107809709809127601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10126581908318452315347205 1898734107809709809127601)
              ·
                refine ⟨1424050580857282356845701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1898734107809709809127601 1424050580857282356845701)
                ·
                  refine ⟨267009483910740441908569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424050580857282356845701 267009483910740441908569)
                  ·
                    rfl

theorem cell22_2339996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_2339996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2339996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2339996 prefixEnd_2339996 := by exact prefixLift 2339996
  have htrace : WordTrace (prefixWord ++ tailWord_2339996) baseStart_2339996 baseEnd_2339996 := by
    simpa [prefixWord, tailWord_2339996, baseEnd_2339996] using wordTrace_append hprefix tailTrace_2339996
  have hstable : (prefixWord ++ tailWord_2339996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2339996).length < 2 ^ (prefixWord ++ tailWord_2339996).sum := by decide
  have hdescent : baseEnd_2339996 < baseStart_2339996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2339996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340056 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 3, 3]
def baseStart_2340056 : Nat := 118140960795 + 2340056 * 2 ^ 59
def prefixEnd_2340056 : Nat := 4983230072969 + 3 ^ 40 * 2340056 * 2
def baseEnd_2340056 : Nat := 801048990958401169225523

theorem tailTrace_2340056 : CollatzResearch.WordTrace tailWord_2340056 prefixEnd_2340056 801048990958401169225523 := by
  unfold tailWord_2340056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42674427005192118296084011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56899236006922824394778681 42674427005192118296084011)
  ·
    refine ⟨64011640507788177444126017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42674427005192118296084011 64011640507788177444126017)
    ·
      refine ⟨48008730380841133083094513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64011640507788177444126017 48008730380841133083094513)
      ·
        refine ⟨36006547785630849812320885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48008730380841133083094513 36006547785630849812320885)
        ·
          refine ⟨3375613854902892169905083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36006547785630849812320885 3375613854902892169905083)
          ·
            refine ⟨5063420782354338254857625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3375613854902892169905083 5063420782354338254857625)
            ·
              refine ⟨3797565586765753691143219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5063420782354338254857625 3797565586765753691143219)
              ·
                refine ⟨5696348380148630536714829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797565586765753691143219 5696348380148630536714829)
                ·
                  refine ⟨2136130642555736451268061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5696348380148630536714829 2136130642555736451268061)
                  ·
                    refine ⟨801048990958401169225523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136130642555736451268061 801048990958401169225523)
                    ·
                      rfl

theorem cell22_2340056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_2340056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340056 prefixEnd_2340056 := by exact prefixLift 2340056
  have htrace : WordTrace (prefixWord ++ tailWord_2340056) baseStart_2340056 baseEnd_2340056 := by
    simpa [prefixWord, tailWord_2340056, baseEnd_2340056] using wordTrace_append hprefix tailTrace_2340056
  have hstable : (prefixWord ++ tailWord_2340056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340056).length < 2 ^ (prefixWord ++ tailWord_2340056).sum := by decide
  have hdescent : baseEnd_2340056 < baseStart_2340056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340099 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 1, 4]
def baseStart_2340099 : Nat := 118140960795 + 2340099 * 2 ^ 59
def prefixEnd_2340099 : Nat := 4983230072969 + 3 ^ 40 * 2340099 * 2
def baseEnd_2340099 : Nat := 801063710737163390400391

theorem tailTrace_2340099 : CollatzResearch.WordTrace tailWord_2340099 prefixEnd_2340099 801063710737163390400391 := by
  unfold tailWord_2340099
  simp only [CollatzResearch.WordTrace]
  refine ⟨85350422349228454935983351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56900281566152303290655567 85350422349228454935983351)
  ·
    refine ⟨128025633523842682403975027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85350422349228454935983351 128025633523842682403975027)
    ·
      refine ⟨192038450285764023605962541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128025633523842682403975027 192038450285764023605962541)
      ·
        refine ⟨72014418857161508852235953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192038450285764023605962541 72014418857161508852235953)
        ·
          refine ⟨54010814142871131639176965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72014418857161508852235953 54010814142871131639176965)
          ·
            refine ⟨10127027651788337182345681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54010814142871131639176965 10127027651788337182345681)
            ·
              refine ⟨7595270738841252886759261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127027651788337182345681 7595270738841252886759261)
              ·
                refine ⟨2848226527065469832534723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7595270738841252886759261 2848226527065469832534723)
                ·
                  refine ⟨4272339790598204748802085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2848226527065469832534723 4272339790598204748802085)
                  ·
                    refine ⟨801063710737163390400391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272339790598204748802085 801063710737163390400391)
                    ·
                      rfl

theorem cell22_2340099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_2340099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340099 prefixEnd_2340099 := by exact prefixLift 2340099
  have htrace : WordTrace (prefixWord ++ tailWord_2340099) baseStart_2340099 baseEnd_2340099 := by
    simpa [prefixWord, tailWord_2340099, baseEnd_2340099] using wordTrace_append hprefix tailTrace_2340099
  have hstable : (prefixWord ++ tailWord_2340099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340099).length < 2 ^ (prefixWord ++ tailWord_2340099).sum := by decide
  have hdescent : baseEnd_2340099 < baseStart_2340099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340144 : List Nat := [2, 1, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_2340144 : Nat := 118140960795 + 2340144 * 2 ^ 59
def prefixEnd_2340144 : Nat := 4983230072969 + 3 ^ 40 * 2340144 * 2
def baseEnd_2340144 : Nat := 801079115156798273025253

theorem tailTrace_2340144 : CollatzResearch.WordTrace tailWord_2340144 prefixEnd_2340144 801079115156798273025253 := by
  unfold tailWord_2340144
  simp only [CollatzResearch.WordTrace]
  refine ⟨42676031817032713810685743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56901375756043618414247657 42676031817032713810685743)
  ·
    refine ⟨64014047725549070716028615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42676031817032713810685743 64014047725549070716028615)
    ·
      refine ⟨96021071588323606074042923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64014047725549070716028615 96021071588323606074042923)
      ·
        refine ⟨144031607382485409111064385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96021071588323606074042923 144031607382485409111064385)
        ·
          refine ⟨108023705536864056833298289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144031607382485409111064385 108023705536864056833298289)
          ·
            refine ⟨81017779152648042624973717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108023705536864056833298289 81017779152648042624973717)
            ·
              refine ⟨3797708397780376998045643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81017779152648042624973717 3797708397780376998045643)
              ·
                refine ⟨5696562596670565497068465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3797708397780376998045643 5696562596670565497068465)
                ·
                  refine ⟨4272421947502924122801349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5696562596670565497068465 4272421947502924122801349)
                  ·
                    refine ⟨801079115156798273025253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272421947502924122801349 801079115156798273025253)
                    ·
                      rfl

theorem cell22_2340144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_2340144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340144 prefixEnd_2340144 := by exact prefixLift 2340144
  have htrace : WordTrace (prefixWord ++ tailWord_2340144) baseStart_2340144 baseEnd_2340144 := by
    simpa [prefixWord, tailWord_2340144, baseEnd_2340144] using wordTrace_append hprefix tailTrace_2340144
  have hstable : (prefixWord ++ tailWord_2340144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340144).length < 2 ^ (prefixWord ++ tailWord_2340144).sum := by decide
  have hdescent : baseEnd_2340144 < baseStart_2340144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340161 : List Nat := [1, 2, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2340161 : Nat := 118140960795 + 2340161 * 2 ^ 59
def prefixEnd_2340161 : Nat := 4983230072969 + 3 ^ 40 * 2340161 * 2
def baseEnd_2340161 : Nat := 801084934604215895350201

theorem tailTrace_2340161 : CollatzResearch.WordTrace tailWord_2340161 prefixEnd_2340161 801084934604215895350201 := by
  unfold tailWord_2340161
  simp only [CollatzResearch.WordTrace]
  refine ⟨85352683675003839524740337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56901789116669226349826891 85352683675003839524740337)
  ·
    refine ⟨64014512756252879643555253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85352683675003839524740337 64014512756252879643555253)
    ·
      refine ⟨6001360570898707466583305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64014512756252879643555253 6001360570898707466583305)
      ·
        refine ⟨4501020428174030599937479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6001360570898707466583305 4501020428174030599937479)
        ·
          refine ⟨6751530642261045899906219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4501020428174030599937479 6751530642261045899906219)
          ·
            refine ⟨10127295963391568849859329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6751530642261045899906219 10127295963391568849859329)
            ·
              refine ⟨7595471972543676637394497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127295963391568849859329 7595471972543676637394497)
              ·
                refine ⟨5696603979407757478045873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7595471972543676637394497 5696603979407757478045873)
                ·
                  refine ⟨4272452984555818108534405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5696603979407757478045873 4272452984555818108534405)
                  ·
                    refine ⟨801084934604215895350201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272452984555818108534405 801084934604215895350201)
                    ·
                      rfl

theorem cell22_2340161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2340161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340161 prefixEnd_2340161 := by exact prefixLift 2340161
  have htrace : WordTrace (prefixWord ++ tailWord_2340161) baseStart_2340161 baseEnd_2340161 := by
    simpa [prefixWord, tailWord_2340161, baseEnd_2340161] using wordTrace_append hprefix tailTrace_2340161
  have hstable : (prefixWord ++ tailWord_2340161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340161).length < 2 ^ (prefixWord ++ tailWord_2340161).sum := by decide
  have hdescent : baseEnd_2340161 < baseStart_2340161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340208 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_2340208 : Nat := 118140960795 + 2340208 * 2 ^ 59
def prefixEnd_2340208 : Nat := 4983230072969 + 3 ^ 40 * 2340208 * 2
def baseEnd_2340208 : Nat := 801101023664723439425057

theorem tailTrace_2340208 : CollatzResearch.WordTrace tailWord_2340208 prefixEnd_2340208 801101023664723439425057 := by
  unfold tailWord_2340208
  simp only [CollatzResearch.WordTrace]
  refine ⟨42677198952916783275850639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56902931937222377701134185 42677198952916783275850639)
  ·
    refine ⟨64015798429375174913775959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42677198952916783275850639 64015798429375174913775959)
    ·
      refine ⟨96023697644062762370663939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64015798429375174913775959 96023697644062762370663939)
      ·
        refine ⟨144035546466094143555995909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96023697644062762370663939 144035546466094143555995909)
        ·
          refine ⟨27006664962392651916749233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144035546466094143555995909 27006664962392651916749233)
          ·
            refine ⟨20254998721794488937561925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27006664962392651916749233 20254998721794488937561925)
            ·
              refine ⟨3797812260336466675792861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20254998721794488937561925 3797812260336466675792861)
              ·
                refine ⟨1424179597626175003422323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3797812260336466675792861 1424179597626175003422323)
                ·
                  refine ⟨2136269396439262505133485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424179597626175003422323 2136269396439262505133485)
                  ·
                    refine ⟨801101023664723439425057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136269396439262505133485 801101023664723439425057)
                    ·
                      rfl

theorem cell22_2340208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_2340208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340208 prefixEnd_2340208 := by exact prefixLift 2340208
  have htrace : WordTrace (prefixWord ++ tailWord_2340208) baseStart_2340208 baseEnd_2340208 := by
    simpa [prefixWord, tailWord_2340208, baseEnd_2340208] using wordTrace_append hprefix tailTrace_2340208
  have hstable : (prefixWord ++ tailWord_2340208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340208).length < 2 ^ (prefixWord ++ tailWord_2340208).sum := by decide
  have hdescent : baseEnd_2340208 < baseStart_2340208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340249 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 6]
def baseStart_2340249 : Nat := 118140960795 + 2340249 * 2 ^ 59
def prefixEnd_2340249 : Nat := 4983230072969 + 3 ^ 40 * 2340249 * 2
def baseEnd_2340249 : Nat := 267038352934204333049977

theorem tailTrace_2340249 : CollatzResearch.WordTrace tailWord_2340249 prefixEnd_2340249 267038352934204333049977 := by
  unfold tailWord_2340249
  simp only [CollatzResearch.WordTrace]
  refine ⟨85355893298685030553943801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56903928865790020369295867 85355893298685030553943801)
  ·
    refine ⟨64016919974013772915457851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85355893298685030553943801 64016919974013772915457851)
    ·
      refine ⟨96025379961020659373186777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64016919974013772915457851 96025379961020659373186777)
      ·
        refine ⟨72019034970765494529890083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96025379961020659373186777 72019034970765494529890083)
        ·
          refine ⟨108028552456148241794835125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72019034970765494529890083 108028552456148241794835125)
          ·
            refine ⟨10127676792763897668265793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108028552456148241794835125 10127676792763897668265793)
            ·
              refine ⟨7595757594572923251199345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10127676792763897668265793 7595757594572923251199345)
              ·
                refine ⟨5696818195929692438399509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7595757594572923251199345 5696818195929692438399509)
                ·
                  refine ⟨267038352934204333049977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5696818195929692438399509 267038352934204333049977)
                  ·
                    rfl

theorem cell22_2340249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_2340249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340249 prefixEnd_2340249 := by exact prefixLift 2340249
  have htrace : WordTrace (prefixWord ++ tailWord_2340249) baseStart_2340249 baseEnd_2340249 := by
    simpa [prefixWord, tailWord_2340249, baseEnd_2340249] using wordTrace_append hprefix tailTrace_2340249
  have hstable : (prefixWord ++ tailWord_2340249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340249).length < 2 ^ (prefixWord ++ tailWord_2340249).sum := by decide
  have hdescent : baseEnd_2340249 < baseStart_2340249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340298 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2340298 : Nat := 118140960795 + 2340298 * 2 ^ 59
def prefixEnd_2340298 : Nat := 4983230072969 + 3 ^ 40 * 2340298 * 2
def baseEnd_2340298 : Nat := 801131832503993204674781

theorem tailTrace_2340298 : CollatzResearch.WordTrace tailWord_2340298 prefixEnd_2340298 801131832503993204674781 := by
  unfold tailWord_2340298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21339420118876877980619387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56905120317005007948318365 21339420118876877980619387)
  ·
    refine ⟨32009130178315316970929081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21339420118876877980619387 32009130178315316970929081)
    ·
      refine ⟨24006847633736487728196811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32009130178315316970929081 24006847633736487728196811)
      ·
        refine ⟨36010271450604731592295217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24006847633736487728196811 36010271450604731592295217)
        ·
          refine ⟨27007703587953548694221413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36010271450604731592295217 27007703587953548694221413)
          ·
            refine ⟨5063944422741290380166515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27007703587953548694221413 5063944422741290380166515)
            ·
              refine ⟨7595916634111935570249773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5063944422741290380166515 7595916634111935570249773)
              ·
                refine ⟨2848468737791975838843665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7595916634111935570249773 2848468737791975838843665)
                ·
                  refine ⟨2136351553343981879132749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2848468737791975838843665 2136351553343981879132749)
                  ·
                    refine ⟨801131832503993204674781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136351553343981879132749 801131832503993204674781)
                    ·
                      rfl

theorem cell22_2340298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2340298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340298 prefixEnd_2340298 := by exact prefixLift 2340298
  have htrace : WordTrace (prefixWord ++ tailWord_2340298) baseStart_2340298 baseEnd_2340298 := by
    simpa [prefixWord, tailWord_2340298, baseEnd_2340298] using wordTrace_append hprefix tailTrace_2340298
  have hstable : (prefixWord ++ tailWord_2340298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340298).length < 2 ^ (prefixWord ++ tailWord_2340298).sum := by decide
  have hdescent : baseEnd_2340298 < baseStart_2340298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340324 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2340324 : Nat := 118140960795 + 2340324 * 2 ^ 59
def prefixEnd_2340324 : Nat := 4983230072969 + 3 ^ 40 * 2340324 * 2
def baseEnd_2340324 : Nat := 801140732835337803524701

theorem tailTrace_2340324 : CollatzResearch.WordTrace tailWord_2340324 prefixEnd_2340324 801140732835337803524701 := by
  unfold tailWord_2340324
  simp only [CollatzResearch.WordTrace]
  refine ⟨42679314386706659181462013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56905752515608878908616017 42679314386706659181462013)
  ·
    refine ⟨16004742895014997193048255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42679314386706659181462013 16004742895014997193048255)
    ·
      refine ⟨24007114342522495789572383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16004742895014997193048255 24007114342522495789572383)
      ·
        refine ⟨36010671513783743684358575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24007114342522495789572383 36010671513783743684358575)
        ·
          refine ⟨54016007270675615526537863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36010671513783743684358575 54016007270675615526537863)
          ·
            refine ⟨81024010906013423289806795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54016007270675615526537863 81024010906013423289806795)
            ·
              refine ⟨121536016359020134934710193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81024010906013423289806795 121536016359020134934710193)
              ·
                refine ⟨91152012269265101201032645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121536016359020134934710193 91152012269265101201032645)
                ·
                  refine ⟨17091002300487206475193621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91152012269265101201032645 17091002300487206475193621)
                  ·
                    refine ⟨801140732835337803524701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17091002300487206475193621 801140732835337803524701)
                    ·
                      rfl

theorem cell22_2340324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2340324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340324 prefixEnd_2340324 := by exact prefixLift 2340324
  have htrace : WordTrace (prefixWord ++ tailWord_2340324) baseStart_2340324 baseEnd_2340324 := by
    simpa [prefixWord, tailWord_2340324, baseEnd_2340324] using wordTrace_append hprefix tailTrace_2340324
  have hstable : (prefixWord ++ tailWord_2340324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340324).length < 2 ^ (prefixWord ++ tailWord_2340324).sum := by decide
  have hdescent : baseEnd_2340324 < baseStart_2340324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340399 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2340399 : Nat := 118140960795 + 2340399 * 2 ^ 59
def prefixEnd_2340399 : Nat := 4983230072969 + 3 ^ 40 * 2340399 * 2
def baseEnd_2340399 : Nat := 801166406868062607899471

theorem tailTrace_2340399 : CollatzResearch.WordTrace tailWord_2340399 prefixEnd_2340399 801166406868062607899471 := by
  unfold tailWord_2340399
  simp only [CollatzResearch.WordTrace]
  refine ⟨85361364248141606171904251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56907576165427737447936167 85361364248141606171904251)
  ·
    refine ⟨128042046372212409257856377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85361364248141606171904251 128042046372212409257856377)
    ·
      refine ⟨96031534779159306943392283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128042046372212409257856377 96031534779159306943392283)
      ·
        refine ⟨144047302168738960415088425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96031534779159306943392283 144047302168738960415088425)
        ·
          refine ⟨108035476626554220311316319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144047302168738960415088425 108035476626554220311316319)
          ·
            refine ⟨162053214939831330466974479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108035476626554220311316319 162053214939831330466974479)
            ·
              refine ⟨243079822409746995700461719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162053214939831330466974479 243079822409746995700461719)
              ·
                refine ⟨364619733614620493550692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243079822409746995700461719 364619733614620493550692579)
                ·
                  refine ⟨546929600421930740326038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364619733614620493550692579 546929600421930740326038869)
                  ·
                    refine ⟨801166406868062607899471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 546929600421930740326038869 801166406868062607899471)
                    ·
                      rfl

theorem cell22_2340399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2340399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340399 prefixEnd_2340399 := by exact prefixLift 2340399
  have htrace : WordTrace (prefixWord ++ tailWord_2340399) baseStart_2340399 baseEnd_2340399 := by
    simpa [prefixWord, tailWord_2340399, baseEnd_2340399] using wordTrace_append hprefix tailTrace_2340399
  have hstable : (prefixWord ++ tailWord_2340399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340399).length < 2 ^ (prefixWord ++ tailWord_2340399).sum := by decide
  have hdescent : baseEnd_2340399 < baseStart_2340399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340431 : List Nat := [1, 1, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2340431 : Nat := 118140960795 + 2340431 * 2 ^ 59
def prefixEnd_2340431 : Nat := 4983230072969 + 3 ^ 40 * 2340431 * 2
def baseEnd_2340431 : Nat := 801177361122025191099373

theorem tailTrace_2340431 : CollatzResearch.WordTrace tailWord_2340431 prefixEnd_2340431 801177361122025191099373 := by
  unfold tailWord_2340431
  simp only [CollatzResearch.WordTrace]
  refine ⟨85362531384025675637069147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56908354256017117091379431 85362531384025675637069147)
  ·
    refine ⟨128043797076038513455603721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85362531384025675637069147 128043797076038513455603721)
    ·
      refine ⟨96032847807028885091702791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128043797076038513455603721 96032847807028885091702791)
      ·
        refine ⟨144049271710543327637554187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96032847807028885091702791 144049271710543327637554187)
        ·
          refine ⟨216073907565814991456331281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144049271710543327637554187 216073907565814991456331281)
          ·
            refine ⟨162055430674361243592248461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216073907565814991456331281 162055430674361243592248461)
            ·
              refine ⟨60770786502885466347093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162055430674361243592248461 60770786502885466347093173)
              ·
                refine ⟨5697261234645512470039985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60770786502885466347093173 5697261234645512470039985)
                ·
                  refine ⟨4272945925984134352529989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5697261234645512470039985 4272945925984134352529989)
                  ·
                    refine ⟨801177361122025191099373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4272945925984134352529989 801177361122025191099373)
                    ·
                      rfl

theorem cell22_2340431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2340431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340431 prefixEnd_2340431 := by exact prefixLift 2340431
  have htrace : WordTrace (prefixWord ++ tailWord_2340431) baseStart_2340431 baseEnd_2340431 := by
    simpa [prefixWord, tailWord_2340431, baseEnd_2340431] using wordTrace_append hprefix tailTrace_2340431
  have hstable : (prefixWord ++ tailWord_2340431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340431).length < 2 ^ (prefixWord ++ tailWord_2340431).sum := by decide
  have hdescent : baseEnd_2340431 < baseStart_2340431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340512 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_2340512 : Nat := 118140960795 + 2340512 * 2 ^ 59
def prefixEnd_2340512 : Nat := 4983230072969 + 3 ^ 40 * 2340512 * 2
def baseEnd_2340512 : Nat := 801205089077367979824125

theorem tailTrace_2340512 : CollatzResearch.WordTrace tailWord_2340512 prefixEnd_2340512 801205089077367979824125 := by
  unfold tailWord_2340512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42682742848366113235383895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56910323797821484313845193 42682742848366113235383895)
  ·
    refine ⟨64024114272549169853075843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42682742848366113235383895 64024114272549169853075843)
    ·
      refine ⟨96036171408823754779613765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64024114272549169853075843 96036171408823754779613765)
      ·
        refine ⟨18006782139154454021177581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96036171408823754779613765 18006782139154454021177581)
        ·
          refine ⟨6752543302182920257941593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18006782139154454021177581 6752543302182920257941593)
          ·
            refine ⟨5064407476637190193456195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6752543302182920257941593 5064407476637190193456195)
            ·
              refine ⟨7596611214955785290184293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5064407476637190193456195 7596611214955785290184293)
              ·
                refine ⟨1424364602804209741909555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7596611214955785290184293 1424364602804209741909555)
                ·
                  refine ⟨2136546904206314612864333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424364602804209741909555 2136546904206314612864333)
                  ·
                    refine ⟨801205089077367979824125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136546904206314612864333 801205089077367979824125)
                    ·
                      rfl

theorem cell22_2340512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_2340512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340512 prefixEnd_2340512 := by exact prefixLift 2340512
  have htrace : WordTrace (prefixWord ++ tailWord_2340512) baseStart_2340512 baseEnd_2340512 := by
    simpa [prefixWord, tailWord_2340512, baseEnd_2340512] using wordTrace_append hprefix tailTrace_2340512
  have hstable : (prefixWord ++ tailWord_2340512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340512).length < 2 ^ (prefixWord ++ tailWord_2340512).sum := by decide
  have hdescent : baseEnd_2340512 < baseStart_2340512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340538 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_2340538 : Nat := 118140960795 + 2340538 * 2 ^ 59
def prefixEnd_2340538 : Nat := 4983230072969 + 3 ^ 40 * 2340538 * 2
def baseEnd_2340538 : Nat := 801213989408712578674045

theorem tailTrace_2340538 : CollatzResearch.WordTrace tailWord_2340538 prefixEnd_2340538 801213989408712578674045 := by
  unfold tailWord_2340538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341608498659508227803567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56910955996425355274142845 21341608498659508227803567)
  ·
    refine ⟨32012412747989262341705351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21341608498659508227803567 32012412747989262341705351)
    ·
      refine ⟨48018619121983893512558027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32012412747989262341705351 48018619121983893512558027)
      ·
        refine ⟨72027928682975840268837041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48018619121983893512558027 72027928682975840268837041)
        ·
          refine ⟨54020946512231880201627781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72027928682975840268837041 54020946512231880201627781)
          ·
            refine ⟨10128927471043477537805209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54020946512231880201627781 10128927471043477537805209)
            ·
              refine ⟨7596695603282608153353907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10128927471043477537805209 7596695603282608153353907)
              ·
                refine ⟨11395043404923912230030861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7596695603282608153353907 11395043404923912230030861)
                ·
                  refine ⟨4273141276846467086261573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11395043404923912230030861 4273141276846467086261573)
                  ·
                    refine ⟨801213989408712578674045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273141276846467086261573 801213989408712578674045)
                    ·
                      rfl

theorem cell22_2340538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_2340538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340538 prefixEnd_2340538 := by exact prefixLift 2340538
  have htrace : WordTrace (prefixWord ++ tailWord_2340538) baseStart_2340538 baseEnd_2340538 := by
    simpa [prefixWord, tailWord_2340538, baseEnd_2340538] using wordTrace_append hprefix tailTrace_2340538
  have hstable : (prefixWord ++ tailWord_2340538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340538).length < 2 ^ (prefixWord ++ tailWord_2340538).sum := by decide
  have hdescent : baseEnd_2340538 < baseStart_2340538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340570 : List Nat := [3, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_2340570 : Nat := 118140960795 + 2340570 * 2 ^ 59
def prefixEnd_2340570 : Nat := 4983230072969 + 3 ^ 40 * 2340570 * 2
def baseEnd_2340570 : Nat := 267074981220891720624649

theorem tailTrace_2340570 : CollatzResearch.WordTrace tailWord_2340570 prefixEnd_2340570 267074981220891720624649 := by
  unfold tailWord_2340570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21341900282630525594094791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56911734087014734917586109 21341900282630525594094791)
  ·
    refine ⟨32012850423945788391142187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21341900282630525594094791 32012850423945788391142187)
    ·
      refine ⟨48019275635918682586713281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32012850423945788391142187 48019275635918682586713281)
      ·
        refine ⟨36014456726939011940034961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48019275635918682586713281 36014456726939011940034961)
        ·
          refine ⟨27010842545204258955026221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36014456726939011940034961 27010842545204258955026221)
          ·
            refine ⟨10129065954451597108134833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27010842545204258955026221 10129065954451597108134833)
            ·
              refine ⟨7596799465838697831101125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10129065954451597108134833 7596799465838697831101125)
              ·
                refine ⟨1424399899844755843331461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7596799465838697831101125 1424399899844755843331461)
                ·
                  refine ⟨267074981220891720624649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424399899844755843331461 267074981220891720624649)
                  ·
                    rfl

theorem cell22_2340570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_2340570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340570 prefixEnd_2340570 := by exact prefixLift 2340570
  have htrace : WordTrace (prefixWord ++ tailWord_2340570) baseStart_2340570 baseEnd_2340570 := by
    simpa [prefixWord, tailWord_2340570, baseEnd_2340570] using wordTrace_append hprefix tailTrace_2340570
  have hstable : (prefixWord ++ tailWord_2340570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340570).length < 2 ^ (prefixWord ++ tailWord_2340570).sum := by decide
  have hdescent : baseEnd_2340570 < baseStart_2340570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340615 : List Nat := [1, 1, 4, 4, 2, 2, 8]
def baseStart_2340615 : Nat := 118140960795 + 2340615 * 2 ^ 59
def prefixEnd_2340615 : Nat := 4983230072969 + 3 ^ 40 * 2340615 * 2
def baseEnd_2340615 : Nat := 29675568447492964611067

theorem tailTrace_2340615 : CollatzResearch.WordTrace tailWord_2340615 prefixEnd_2340615 29675568447492964611067 := by
  unfold tailWord_2340615
  simp only [CollatzResearch.WordTrace]
  refine ⟨85369242415359075061767299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56912828276906050041178199 85369242415359075061767299)
  ·
    refine ⟨128053863623038612592650949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85369242415359075061767299 128053863623038612592650949)
    ·
      refine ⟨24010099429319739861122053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128053863623038612592650949 24010099429319739861122053)
      ·
        refine ⟨4501893642997451223960385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24010099429319739861122053 4501893642997451223960385)
        ·
          refine ⟨3376420232248088417970289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4501893642997451223960385 3376420232248088417970289)
          ·
            refine ⟨2532315174186066313477717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3376420232248088417970289 2532315174186066313477717)
            ·
              refine ⟨29675568447492964611067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2532315174186066313477717 29675568447492964611067)
              ·
                rfl

theorem cell22_2340615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 8].length) (baseStart_2340615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340615 prefixEnd_2340615 := by exact prefixLift 2340615
  have htrace : WordTrace (prefixWord ++ tailWord_2340615) baseStart_2340615 baseEnd_2340615 := by
    simpa [prefixWord, tailWord_2340615, baseEnd_2340615] using wordTrace_append hprefix tailTrace_2340615
  have hstable : (prefixWord ++ tailWord_2340615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340615).length < 2 ^ (prefixWord ++ tailWord_2340615).sum := by decide
  have hdescent : baseEnd_2340615 < baseStart_2340615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340688 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_2340688 : Nat := 118140960795 + 2340688 * 2 ^ 59
def prefixEnd_2340688 : Nat := 4983230072969 + 3 ^ 40 * 2340688 * 2
def baseEnd_2340688 : Nat := 267088445824720729141195

theorem tailTrace_2340688 : CollatzResearch.WordTrace tailWord_2340688 prefixEnd_2340688 267088445824720729141195 := by
  unfold tailWord_2340688
  simp only [CollatzResearch.WordTrace]
  refine ⟨42685952472047304264587359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56914603296063072352783145 42685952472047304264587359)
  ·
    refine ⟨64028928708070956396881039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42685952472047304264587359 64028928708070956396881039)
    ·
      refine ⟨96043393062106434595321559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64028928708070956396881039 96043393062106434595321559)
      ·
        refine ⟨144065089593159651892982339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96043393062106434595321559 144065089593159651892982339)
        ·
          refine ⟨216097634389739477839473509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144065089593159651892982339 216097634389739477839473509)
          ·
            refine ⟨40518306448076152094901283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 216097634389739477839473509 40518306448076152094901283)
            ·
              refine ⟨60777459672114228142351925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40518306448076152094901283 60777459672114228142351925)
              ·
                refine ⟨5697886844260708888345493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60777459672114228142351925 5697886844260708888345493)
                ·
                  refine ⟨267088445824720729141195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5697886844260708888345493 267088445824720729141195)
                  ·
                    rfl

theorem cell22_2340688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_2340688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340688 prefixEnd_2340688 := by exact prefixLift 2340688
  have htrace : WordTrace (prefixWord ++ tailWord_2340688) baseStart_2340688 baseEnd_2340688 := by
    simpa [prefixWord, tailWord_2340688, baseEnd_2340688] using wordTrace_append hprefix tailTrace_2340688
  have hstable : (prefixWord ++ tailWord_2340688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340688).length < 2 ^ (prefixWord ++ tailWord_2340688).sum := by decide
  have hdescent : baseEnd_2340688 < baseStart_2340688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340690 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2340690 : Nat := 118140960795 + 2340690 * 2 ^ 59
def prefixEnd_2340690 : Nat := 4983230072969 + 3 ^ 40 * 2340690 * 2
def baseEnd_2340690 : Nat := 801266022115034848873579

theorem tailTrace_2340690 : CollatzResearch.WordTrace tailWord_2340690 prefixEnd_2340690 801266022115034848873579 := by
  unfold tailWord_2340690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21342994472521840717686881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56914651926724908580498349 21342994472521840717686881)
  ·
    refine ⟨16007245854391380538265161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21342994472521840717686881 16007245854391380538265161)
    ·
      refine ⟨12005434390793535403698871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16007245854391380538265161 12005434390793535403698871)
      ·
        refine ⟨18008151586190303105548307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12005434390793535403698871 18008151586190303105548307)
        ·
          refine ⟨27012227379285454658322461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18008151586190303105548307 27012227379285454658322461)
          ·
            refine ⟨10129585267232045496870923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27012227379285454658322461 10129585267232045496870923)
            ·
              refine ⟨15194377900848068245306385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10129585267232045496870923 15194377900848068245306385)
              ·
                refine ⟨11395783425636051183979789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15194377900848068245306385 11395783425636051183979789)
                ·
                  refine ⟨4273418784613519193992421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11395783425636051183979789 4273418784613519193992421)
                  ·
                    refine ⟨801266022115034848873579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273418784613519193992421 801266022115034848873579)
                    ·
                      rfl

theorem cell22_2340690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2340690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340690 prefixEnd_2340690 := by exact prefixLift 2340690
  have htrace : WordTrace (prefixWord ++ tailWord_2340690) baseStart_2340690 baseEnd_2340690 := by
    simpa [prefixWord, tailWord_2340690, baseEnd_2340690] using wordTrace_append hprefix tailTrace_2340690
  have hstable : (prefixWord ++ tailWord_2340690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340690).length < 2 ^ (prefixWord ++ tailWord_2340690).sum := by decide
  have hdescent : baseEnd_2340690 < baseStart_2340690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340720 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_2340720 : Nat := 118140960795 + 2340720 * 2 ^ 59
def prefixEnd_2340720 : Nat := 4983230072969 + 3 ^ 40 * 2340720 * 2
def baseEnd_2340720 : Nat := 801276291728124770623487

theorem tailTrace_2340720 : CollatzResearch.WordTrace tailWord_2340720 prefixEnd_2340720 801276291728124770623487 := by
  unfold tailWord_2340720
  simp only [CollatzResearch.WordTrace]
  refine ⟨42686536039989338997169807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56915381386652451996226409 42686536039989338997169807)
  ·
    refine ⟨64029804059984008495754711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42686536039989338997169807 64029804059984008495754711)
    ·
      refine ⟨96044706089976012743632067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64029804059984008495754711 96044706089976012743632067)
      ·
        refine ⟨144067059134964019115448101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96044706089976012743632067 144067059134964019115448101)
        ·
          refine ⟨27012573587805753584146519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144067059134964019115448101 27012573587805753584146519)
          ·
            refine ⟨40518860381708630376219779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27012573587805753584146519 40518860381708630376219779)
            ·
              refine ⟨60778290572562945564329669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40518860381708630376219779 60778290572562945564329669)
              ·
                refine ⟨11395929482355552293311813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60778290572562945564329669 11395929482355552293311813)
                ·
                  refine ⟨2136736777941666054995965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11395929482355552293311813 2136736777941666054995965)
                  ·
                    refine ⟨801276291728124770623487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136736777941666054995965 801276291728124770623487)
                    ·
                      rfl

theorem cell22_2340720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_2340720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340720 prefixEnd_2340720 := by exact prefixLift 2340720
  have htrace : WordTrace (prefixWord ++ tailWord_2340720) baseStart_2340720 baseEnd_2340720 := by
    simpa [prefixWord, tailWord_2340720, baseEnd_2340720] using wordTrace_append hprefix tailTrace_2340720
  have hstable : (prefixWord ++ tailWord_2340720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340720).length < 2 ^ (prefixWord ++ tailWord_2340720).sum := by decide
  have hdescent : baseEnd_2340720 < baseStart_2340720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340754 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2340754 : Nat := 118140960795 + 2340754 * 2 ^ 59
def prefixEnd_2340754 : Nat := 4983230072969 + 3 ^ 40 * 2340754 * 2
def baseEnd_2340754 : Nat := 801287930622960015273383

theorem tailTrace_2340754 : CollatzResearch.WordTrace tailWord_2340754 prefixEnd_2340754 801287930622960015273383 := by
  unfold tailWord_2340754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21343578040463875450269329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56916208107903667867384877 21343578040463875450269329)
  ·
    refine ⟨16007683530347906587701997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21343578040463875450269329 16007683530347906587701997)
    ·
      refine ⟨6002881323880464970388249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16007683530347906587701997 6002881323880464970388249)
      ·
        refine ⟨4502160992910348727791187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6002881323880464970388249 4502160992910348727791187)
        ·
          refine ⟨6753241489365523091686781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502160992910348727791187 6753241489365523091686781)
          ·
            refine ⟨2532465558512071159382543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6753241489365523091686781 2532465558512071159382543)
            ·
              refine ⟨3798698337768106739073815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532465558512071159382543 3798698337768106739073815)
              ·
                refine ⟨5698047506652160108610723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798698337768106739073815 5698047506652160108610723)
                ·
                  refine ⟨8547071259978240162916085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698047506652160108610723 8547071259978240162916085)
                  ·
                    refine ⟨801287930622960015273383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8547071259978240162916085 801287930622960015273383)
                    ·
                      rfl

theorem cell22_2340754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2340754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340754 prefixEnd_2340754 := by exact prefixLift 2340754
  have htrace : WordTrace (prefixWord ++ tailWord_2340754) baseStart_2340754 baseEnd_2340754 := by
    simpa [prefixWord, tailWord_2340754, baseEnd_2340754] using wordTrace_append hprefix tailTrace_2340754
  have hstable : (prefixWord ++ tailWord_2340754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340754).length < 2 ^ (prefixWord ++ tailWord_2340754).sum := by decide
  have hdescent : baseEnd_2340754 < baseStart_2340754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340758 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2340758 : Nat := 118140960795 + 2340758 * 2 ^ 59
def prefixEnd_2340758 : Nat := 4983230072969 + 3 ^ 40 * 2340758 * 2
def baseEnd_2340758 : Nat := 801289299904705338173371

theorem tailTrace_2340758 : CollatzResearch.WordTrace tailWord_2340758 prefixEnd_2340758 801289299904705338173371 := by
  unfold tailWord_2340758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335903628365063155263933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56916305369227340322815285 5335903628365063155263933)
  ·
    refine ⟨2000963860636898683223975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5335903628365063155263933 2000963860636898683223975)
    ·
      refine ⟨3001445790955348024835963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000963860636898683223975 3001445790955348024835963)
      ·
        refine ⟨4502168686433022037253945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001445790955348024835963 4502168686433022037253945)
        ·
          refine ⟨3376626514824766527940459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502168686433022037253945 3376626514824766527940459)
          ·
            refine ⟨5064939772237149791910689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3376626514824766527940459 5064939772237149791910689)
            ·
              refine ⟨3798704829177862343933017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5064939772237149791910689 3798704829177862343933017)
              ·
                refine ⟨2849028621883396757949763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798704829177862343933017 2849028621883396757949763)
                ·
                  refine ⟨4273542932825095136924645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849028621883396757949763 4273542932825095136924645)
                  ·
                    refine ⟨801289299904705338173371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273542932825095136924645 801289299904705338173371)
                    ·
                      rfl

theorem cell22_2340758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2340758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340758 prefixEnd_2340758 := by exact prefixLift 2340758
  have htrace : WordTrace (prefixWord ++ tailWord_2340758) baseStart_2340758 baseEnd_2340758 := by
    simpa [prefixWord, tailWord_2340758, baseEnd_2340758] using wordTrace_append hprefix tailTrace_2340758
  have hstable : (prefixWord ++ tailWord_2340758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340758).length < 2 ^ (prefixWord ++ tailWord_2340758).sum := by decide
  have hdescent : baseEnd_2340758 < baseStart_2340758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340810 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_2340810 : Nat := 118140960795 + 2340810 * 2 ^ 59
def prefixEnd_2340810 : Nat := 4983230072969 + 3 ^ 40 * 2340810 * 2
def baseEnd_2340810 : Nat := 801307100567394535873211

theorem tailTrace_2340810 : CollatzResearch.WordTrace tailWord_2340810 prefixEnd_2340810 801307100567394535873211 := by
  unfold tailWord_2340810
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344088662413155841278971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56917569766435082243410589 21344088662413155841278971)
  ·
    refine ⟨32016132993619733761918457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344088662413155841278971 32016132993619733761918457)
    ·
      refine ⟨24012099745214800321438843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32016132993619733761918457 24012099745214800321438843)
      ·
        refine ⟨36018149617822200482158265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24012099745214800321438843 36018149617822200482158265)
        ·
          refine ⟨27013612213366650361618699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36018149617822200482158265 27013612213366650361618699)
          ·
            refine ⟨40520418320049975542428049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27013612213366650361618699 40520418320049975542428049)
            ·
              refine ⟨30390313740037481656821037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40520418320049975542428049 30390313740037481656821037)
              ·
                refine ⟨11396367652514055621307889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30390313740037481656821037 11396367652514055621307889)
                ·
                  refine ⟨8547275739385541715980917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11396367652514055621307889 8547275739385541715980917)
                  ·
                    refine ⟨801307100567394535873211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8547275739385541715980917 801307100567394535873211)
                    ·
                      rfl

theorem cell22_2340810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_2340810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340810 prefixEnd_2340810 := by exact prefixLift 2340810
  have htrace : WordTrace (prefixWord ++ tailWord_2340810) baseStart_2340810 baseEnd_2340810 := by
    simpa [prefixWord, tailWord_2340810, baseEnd_2340810] using wordTrace_append hprefix tailTrace_2340810
  have hstable : (prefixWord ++ tailWord_2340810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340810).length < 2 ^ (prefixWord ++ tailWord_2340810).sum := by decide
  have hdescent : baseEnd_2340810 < baseStart_2340810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340812 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_2340812 : Nat := 118140960795 + 2340812 * 2 ^ 59
def prefixEnd_2340812 : Nat := 4983230072969 + 3 ^ 40 * 2340812 * 2
def baseEnd_2340812 : Nat := 267102595069422399107735

theorem tailTrace_2340812 : CollatzResearch.WordTrace tailWord_2340812 prefixEnd_2340812 267102595069422399107735 := by
  unfold tailWord_2340812
  simp only [CollatzResearch.WordTrace]
  refine ⟨42688213797822688853344345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56917618397096918471125793 42688213797822688853344345)
  ·
    refine ⟨32016160348367016640008259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42688213797822688853344345 32016160348367016640008259)
    ·
      refine ⟨48024240522550524960012389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32016160348367016640008259 48024240522550524960012389)
      ·
        refine ⟨9004545097978223430002323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48024240522550524960012389 9004545097978223430002323)
        ·
          refine ⟨13506817646967335145003485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9004545097978223430002323 13506817646967335145003485)
          ·
            refine ⟨5065056617612750679376307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13506817646967335145003485 5065056617612750679376307)
            ·
              refine ⟨7597584926419126019064461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5065056617612750679376307 7597584926419126019064461)
              ·
                refine ⟨2849094347407172257149173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7597584926419126019064461 2849094347407172257149173)
                ·
                  refine ⟨267102595069422399107735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849094347407172257149173 267102595069422399107735)
                  ·
                    rfl

theorem cell22_2340812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_2340812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340812 prefixEnd_2340812 := by exact prefixLift 2340812
  have htrace : WordTrace (prefixWord ++ tailWord_2340812) baseStart_2340812 baseEnd_2340812 := by
    simpa [prefixWord, tailWord_2340812, baseEnd_2340812] using wordTrace_append hprefix tailTrace_2340812
  have hstable : (prefixWord ++ tailWord_2340812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340812).length < 2 ^ (prefixWord ++ tailWord_2340812).sum := by decide
  have hdescent : baseEnd_2340812 < baseStart_2340812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340872 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2340872 : Nat := 118140960795 + 2340872 * 2 ^ 59
def prefixEnd_2340872 : Nat := 4983230072969 + 3 ^ 40 * 2340872 * 2
def baseEnd_2340872 : Nat := 801328324434447040823021

theorem tailTrace_2340872 : CollatzResearch.WordTrace tailWord_2340872 prefixEnd_2340872 801328324434447040823021 := by
  unfold tailWord_2340872
  simp only [CollatzResearch.WordTrace]
  refine ⟨42689307987714003976936435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56919077316952005302581913 42689307987714003976936435)
  ·
    refine ⟨64033961981571005965404653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42689307987714003976936435 64033961981571005965404653)
    ·
      refine ⟨24012735743089127237026745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64033961981571005965404653 24012735743089127237026745)
      ·
        refine ⟨18009551807316845427770059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24012735743089127237026745 18009551807316845427770059)
        ·
          refine ⟨27014327710975268141655089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18009551807316845427770059 27014327710975268141655089)
          ·
            refine ⟨20260745783231451106241317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27014327710975268141655089 20260745783231451106241317)
            ·
              refine ⟨3798889834355897082420247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20260745783231451106241317 3798889834355897082420247)
              ·
                refine ⟨5698334751533845623630371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3798889834355897082420247 5698334751533845623630371)
                ·
                  refine ⟨8547502127300768435445557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698334751533845623630371 8547502127300768435445557)
                  ·
                    refine ⟨801328324434447040823021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8547502127300768435445557 801328324434447040823021)
                    ·
                      rfl

theorem cell22_2340872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2340872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340872 prefixEnd_2340872 := by exact prefixLift 2340872
  have htrace : WordTrace (prefixWord ++ tailWord_2340872) baseStart_2340872 baseEnd_2340872 := by
    simpa [prefixWord, tailWord_2340872, baseEnd_2340872] using wordTrace_append hprefix tailTrace_2340872
  have hstable : (prefixWord ++ tailWord_2340872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340872).length < 2 ^ (prefixWord ++ tailWord_2340872).sum := by decide
  have hdescent : baseEnd_2340872 < baseStart_2340872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340906 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2340906 : Nat := 118140960795 + 2340906 * 2 ^ 59
def prefixEnd_2340906 : Nat := 4983230072969 + 3 ^ 40 * 2340906 * 2
def baseEnd_2340906 : Nat := 801339963329282285472917

theorem tailTrace_2340906 : CollatzResearch.WordTrace tailWord_2340906 prefixEnd_2340906 801339963329282285472917 := by
  unfold tailWord_2340906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21344964014326207940152643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56919904038203221173740381 21344964014326207940152643)
  ·
    refine ⟨32017446021489311910228965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21344964014326207940152643 32017446021489311910228965)
    ·
      refine ⟨6003271129029245983167931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32017446021489311910228965 6003271129029245983167931)
      ·
        refine ⟨9004906693543868974751897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003271129029245983167931 9004906693543868974751897)
        ·
          refine ⟨6753680020157901731063923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9004906693543868974751897 6753680020157901731063923)
          ·
            refine ⟨10130520030236852596595885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6753680020157901731063923 10130520030236852596595885)
            ·
              refine ⟨3798945011338819723723457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10130520030236852596595885 3798945011338819723723457)
              ·
                refine ⟨2849208758504114792792593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3798945011338819723723457 2849208758504114792792593)
                ·
                  refine ⟨2136906568878086094594445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2849208758504114792792593 2136906568878086094594445)
                  ·
                    refine ⟨801339963329282285472917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136906568878086094594445 801339963329282285472917)
                    ·
                      rfl

theorem cell22_2340906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2340906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340906 prefixEnd_2340906 := by exact prefixLift 2340906
  have htrace : WordTrace (prefixWord ++ tailWord_2340906) baseStart_2340906 baseEnd_2340906 := by
    simpa [prefixWord, tailWord_2340906, baseEnd_2340906] using wordTrace_append hprefix tailTrace_2340906
  have hstable : (prefixWord ++ tailWord_2340906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340906).length < 2 ^ (prefixWord ++ tailWord_2340906).sum := by decide
  have hdescent : baseEnd_2340906 < baseStart_2340906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340915 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_2340915 : Nat := 118140960795 + 2340915 * 2 ^ 59
def prefixEnd_2340915 : Nat := 4983230072969 + 3 ^ 40 * 2340915 * 2
def baseEnd_2340915 : Nat := 801343044213209261997889

theorem tailTrace_2340915 : CollatzResearch.WordTrace tailWord_2340915 prefixEnd_2340915 801343044213209261997889 := by
  unfold tailWord_2340915
  simp only [CollatzResearch.WordTrace]
  refine ⟨85380184314272226297688199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56920122876181484198458799 85380184314272226297688199)
  ·
    refine ⟨128070276471408339446532299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85380184314272226297688199 128070276471408339446532299)
    ·
      refine ⟨192105414707112509169798449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128070276471408339446532299 192105414707112509169798449)
      ·
        refine ⟨144079061030334381877348837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192105414707112509169798449 144079061030334381877348837)
        ·
          refine ⟨27014823943187696602002907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144079061030334381877348837 27014823943187696602002907)
          ·
            refine ⟨40522235914781544903004361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27014823943187696602002907 40522235914781544903004361)
            ·
              refine ⟨30391676936086158677253271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40522235914781544903004361 30391676936086158677253271)
              ·
                refine ⟨45587515404129238015879907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30391676936086158677253271 45587515404129238015879907)
                ·
                  refine ⟨68381273106193857023819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45587515404129238015879907 68381273106193857023819861)
                  ·
                    refine ⟨801343044213209261997889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68381273106193857023819861 801343044213209261997889)
                    ·
                      rfl

theorem cell22_2340915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_2340915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340915 prefixEnd_2340915 := by exact prefixLift 2340915
  have htrace : WordTrace (prefixWord ++ tailWord_2340915) baseStart_2340915 baseEnd_2340915 := by
    simpa [prefixWord, tailWord_2340915, baseEnd_2340915] using wordTrace_append hprefix tailTrace_2340915
  have hstable : (prefixWord ++ tailWord_2340915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340915).length < 2 ^ (prefixWord ++ tailWord_2340915).sum := by decide
  have hdescent : baseEnd_2340915 < baseStart_2340915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340934 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2340934 : Nat := 118140960795 + 2340934 * 2 ^ 59
def prefixEnd_2340934 : Nat := 4983230072969 + 3 ^ 40 * 2340934 * 2
def baseEnd_2340934 : Nat := 801349548301499545772831

theorem tailTrace_2340934 : CollatzResearch.WordTrace tailWord_2340934 prefixEnd_2340934 801349548301499545772831 := by
  unfold tailWord_2340934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668152415662606016957183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56920584867468928361753237 2668152415662606016957183)
  ·
    refine ⟨4002228623493909025435775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2668152415662606016957183 4002228623493909025435775)
    ·
      refine ⟨6003342935240863538153663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4002228623493909025435775 6003342935240863538153663)
      ·
        refine ⟨9005014402861295307230495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6003342935240863538153663 9005014402861295307230495)
        ·
          refine ⟨13507521604291942960845743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9005014402861295307230495 13507521604291942960845743)
          ·
            refine ⟨20261282406437914441268615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13507521604291942960845743 20261282406437914441268615)
            ·
              refine ⟨30391923609656871661902923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20261282406437914441268615 30391923609656871661902923)
              ·
                refine ⟨45587885414485307492854385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30391923609656871661902923 45587885414485307492854385)
                ·
                  refine ⟨34190914060863980619640789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45587885414485307492854385 34190914060863980619640789)
                  ·
                    refine ⟨801349548301499545772831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34190914060863980619640789 801349548301499545772831)
                    ·
                      rfl

theorem cell22_2340934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2340934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340934 prefixEnd_2340934 := by exact prefixLift 2340934
  have htrace : WordTrace (prefixWord ++ tailWord_2340934) baseStart_2340934 baseEnd_2340934 := by
    simpa [prefixWord, tailWord_2340934, baseEnd_2340934] using wordTrace_append hprefix tailTrace_2340934
  have hstable : (prefixWord ++ tailWord_2340934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340934).length < 2 ^ (prefixWord ++ tailWord_2340934).sum := by decide
  have hdescent : baseEnd_2340934 < baseStart_2340934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340951 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 1, 3]
def baseStart_2340951 : Nat := 118140960795 + 2340951 * 2 ^ 59
def prefixEnd_2340951 : Nat := 4983230072969 + 3 ^ 40 * 2340951 * 2
def baseEnd_2340951 : Nat := 801355367748917168097779

theorem tailTrace_2340951 : CollatzResearch.WordTrace tailWord_2340951 prefixEnd_2340951 801355367748917168097779 := by
  unfold tailWord_2340951
  simp only [CollatzResearch.WordTrace]
  refine ⟨85381497342141804445998707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56920998228094536297332471 85381497342141804445998707)
  ·
    refine ⟨128072246013212706668998061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85381497342141804445998707 128072246013212706668998061)
    ·
      refine ⟨48027092254954765000874273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128072246013212706668998061 48027092254954765000874273)
      ·
        refine ⟨36020319191216073750655705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48027092254954765000874273 36020319191216073750655705)
        ·
          refine ⟨27015239393412055312991779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36020319191216073750655705 27015239393412055312991779)
          ·
            refine ⟨40522859090118082969487669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27015239393412055312991779 40522859090118082969487669)
            ·
              refine ⟨3799018039698570278389469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40522859090118082969487669 3799018039698570278389469)
              ·
                refine ⟨1424631764886963854396051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3799018039698570278389469 1424631764886963854396051)
                ·
                  refine ⟨2136947647330445781594077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1424631764886963854396051 2136947647330445781594077)
                  ·
                    refine ⟨801355367748917168097779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2136947647330445781594077 801355367748917168097779)
                    ·
                      rfl

theorem cell22_2340951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_2340951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340951 prefixEnd_2340951 := by exact prefixLift 2340951
  have htrace : WordTrace (prefixWord ++ tailWord_2340951) baseStart_2340951 baseEnd_2340951 := by
    simpa [prefixWord, tailWord_2340951, baseEnd_2340951] using wordTrace_append hprefix tailTrace_2340951
  have hstable : (prefixWord ++ tailWord_2340951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340951).length < 2 ^ (prefixWord ++ tailWord_2340951).sum := by decide
  have hdescent : baseEnd_2340951 < baseStart_2340951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2340977 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2340977 : Nat := 118140960795 + 2340977 * 2 ^ 59
def prefixEnd_2340977 : Nat := 4983230072969 + 3 ^ 40 * 2340977 * 2
def baseEnd_2340977 : Nat := 801364268080261766947699

theorem tailTrace_2340977 : CollatzResearch.WordTrace tailWord_2340977 prefixEnd_2340977 801364268080261766947699 := by
  unfold tailWord_2340977
  simp only [CollatzResearch.WordTrace]
  refine ⟨85382445640047610886445185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56921630426698407257630123 85382445640047610886445185)
  ·
    refine ⟨64036834230035708164833889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85382445640047610886445185 64036834230035708164833889)
    ·
      refine ⟨48027625672526781123625417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64036834230035708164833889 48027625672526781123625417)
      ·
        refine ⟨36020719254395085842719063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48027625672526781123625417 36020719254395085842719063)
        ·
          refine ⟨54031078881592628764078595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36020719254395085842719063 54031078881592628764078595)
          ·
            refine ⟨81046618322388943146117893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54031078881592628764078595 81046618322388943146117893)
            ·
              refine ⟨15196240935447926839897105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81046618322388943146117893 15196240935447926839897105)
              ·
                refine ⟨11397180701585945129922829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15196240935447926839897105 11397180701585945129922829)
                ·
                  refine ⟨4273942763094729423721061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11397180701585945129922829 4273942763094729423721061)
                  ·
                    refine ⟨801364268080261766947699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4273942763094729423721061 801364268080261766947699)
                    ·
                      rfl

theorem cell22_2340977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2340977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2340977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2340977 prefixEnd_2340977 := by exact prefixLift 2340977
  have htrace : WordTrace (prefixWord ++ tailWord_2340977) baseStart_2340977 baseEnd_2340977 := by
    simpa [prefixWord, tailWord_2340977, baseEnd_2340977] using wordTrace_append hprefix tailTrace_2340977
  have hstable : (prefixWord ++ tailWord_2340977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2340977).length < 2 ^ (prefixWord ++ tailWord_2340977).sum := by decide
  have hdescent : baseEnd_2340977 < baseStart_2340977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2340977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341041 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2341041 : Nat := 118140960795 + 2341041 * 2 ^ 59
def prefixEnd_2341041 : Nat := 4983230072969 + 3 ^ 40 * 2341041 * 2
def baseEnd_2341041 : Nat := 801386176588186933347503

theorem tailTrace_2341041 : CollatzResearch.WordTrace tailWord_2341041 prefixEnd_2341041 801386176588186933347503 := by
  unfold tailWord_2341041
  simp only [CollatzResearch.WordTrace]
  refine ⟨85384779911815749816774977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56923186607877166544516651 85384779911815749816774977)
  ·
    refine ⟨64038584933861812362581233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85384779911815749816774977 64038584933861812362581233)
    ·
      refine ⟨48028938700396359271935925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64038584933861812362581233 48028938700396359271935925)
      ·
        refine ⟨4502713003162158681743993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48028938700396359271935925 4502713003162158681743993)
        ·
          refine ⟨3377034752371619011307995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4502713003162158681743993 3377034752371619011307995)
          ·
            refine ⟨5065552128557428516961993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377034752371619011307995 5065552128557428516961993)
            ·
              refine ⟨3799164096418071387721495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5065552128557428516961993 3799164096418071387721495)
              ·
                refine ⟨5698746144627107081582243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799164096418071387721495 5698746144627107081582243)
                ·
                  refine ⟨8548119216940660622373365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698746144627107081582243 8548119216940660622373365)
                  ·
                    refine ⟨801386176588186933347503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8548119216940660622373365 801386176588186933347503)
                    ·
                      rfl

theorem cell22_2341041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2341041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341041 prefixEnd_2341041 := by exact prefixLift 2341041
  have htrace : WordTrace (prefixWord ++ tailWord_2341041) baseStart_2341041 baseEnd_2341041 := by
    simpa [prefixWord, tailWord_2341041, baseEnd_2341041] using wordTrace_append hprefix tailTrace_2341041
  have hstable : (prefixWord ++ tailWord_2341041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341041).length < 2 ^ (prefixWord ++ tailWord_2341041).sum := by decide
  have hdescent : baseEnd_2341041 < baseStart_2341041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341056 : List Nat := [2, 1, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_2341056 : Nat := 118140960795 + 2341056 * 2 ^ 59
def prefixEnd_2341056 : Nat := 4983230072969 + 3 ^ 40 * 2341056 * 2
def baseEnd_2341056 : Nat := 801391311394731894222457

theorem tailTrace_2341056 : CollatzResearch.WordTrace tailWord_2341056 prefixEnd_2341056 801391311394731894222457 := by
  unfold tailWord_2341056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42692663503380703689285511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56923551337840938252380681 42692663503380703689285511)
  ·
    refine ⟨64038995255071055533928267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42692663503380703689285511 64038995255071055533928267)
    ·
      refine ⟨96058492882606583300892401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64038995255071055533928267 96058492882606583300892401)
      ·
        refine ⟨72043869661954937475669301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96058492882606583300892401 72043869661954937475669301)
        ·
          refine ⟨6754112780808275388343997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72043869661954937475669301 6754112780808275388343997)
          ·
            refine ⟨2532792292803103270628999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6754112780808275388343997 2532792292803103270628999)
            ·
              refine ⟨3799188439204654905943499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2532792292803103270628999 3799188439204654905943499)
              ·
                refine ⟨5698782658806982358915249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799188439204654905943499 5698782658806982358915249)
                ·
                  refine ⟨4274086994105236769186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5698782658806982358915249 4274086994105236769186437)
                  ·
                    refine ⟨801391311394731894222457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274086994105236769186437 801391311394731894222457)
                    ·
                      rfl

theorem cell22_2341056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_2341056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341056 prefixEnd_2341056 := by exact prefixLift 2341056
  have htrace : WordTrace (prefixWord ++ tailWord_2341056) baseStart_2341056 baseEnd_2341056 := by
    simpa [prefixWord, tailWord_2341056, baseEnd_2341056] using wordTrace_append hprefix tailTrace_2341056
  have hstable : (prefixWord ++ tailWord_2341056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341056).length < 2 ^ (prefixWord ++ tailWord_2341056).sum := by decide
  have hdescent : baseEnd_2341056 < baseStart_2341056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341058 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2341058 : Nat := 118140960795 + 2341058 * 2 ^ 59
def prefixEnd_2341058 : Nat := 4983230072969 + 3 ^ 40 * 2341058 * 2
def baseEnd_2341058 : Nat := 801391996035604555672451

theorem tailTrace_2341058 : CollatzResearch.WordTrace tailWord_2341058 prefixEnd_2341058 801391996035604555672451 := by
  unfold tailWord_2341058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21346349988188540430035957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56923599968502774480095885 21346349988188540430035957)
  ·
    refine ⟨2001220311392675665315871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21346349988188540430035957 2001220311392675665315871)
    ·
      refine ⟨3001830467089013497973807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001220311392675665315871 3001830467089013497973807)
      ·
        refine ⟨4502745700633520246960711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001830467089013497973807 4502745700633520246960711)
        ·
          refine ⟨6754118550950280370441067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502745700633520246960711 6754118550950280370441067)
          ·
            refine ⟨10131177826425420555661601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754118550950280370441067 10131177826425420555661601)
            ·
              refine ⟨7598383369819065416746201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10131177826425420555661601 7598383369819065416746201)
              ·
                refine ⟨5698787527364299062559651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7598383369819065416746201 5698787527364299062559651)
                ·
                  refine ⟨8548181291046448593839477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5698787527364299062559651 8548181291046448593839477)
                  ·
                    refine ⟨801391996035604555672451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8548181291046448593839477 801391996035604555672451)
                    ·
                      rfl

theorem cell22_2341058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2341058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341058 prefixEnd_2341058 := by exact prefixLift 2341058
  have htrace : WordTrace (prefixWord ++ tailWord_2341058) baseStart_2341058 baseEnd_2341058 := by
    simpa [prefixWord, tailWord_2341058, baseEnd_2341058] using wordTrace_append hprefix tailTrace_2341058
  have hstable : (prefixWord ++ tailWord_2341058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341058).length < 2 ^ (prefixWord ++ tailWord_2341058).sum := by decide
  have hdescent : baseEnd_2341058 < baseStart_2341058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341112 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2341112 : Nat := 118140960795 + 2341112 * 2 ^ 59
def prefixEnd_2341112 : Nat := 4983230072969 + 3 ^ 40 * 2341112 * 2
def baseEnd_2341112 : Nat := 801410481339166414822285

theorem tailTrace_2341112 : CollatzResearch.WordTrace tailWord_2341112 prefixEnd_2341112 801410481339166414822285 := by
  unfold tailWord_2341112
  simp only [CollatzResearch.WordTrace]
  refine ⟨42693684747279264471304795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56924912996372352628406393 42693684747279264471304795)
  ·
    refine ⟨64040527120918896706957193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42693684747279264471304795 64040527120918896706957193)
    ·
      refine ⟨48030395340689172530217895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64040527120918896706957193 48030395340689172530217895)
      ·
        refine ⟨72045593011033758795326843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48030395340689172530217895 72045593011033758795326843)
        ·
          refine ⟨108068389516550638192990265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72045593011033758795326843 108068389516550638192990265)
          ·
            refine ⟨81051292137412978644742699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108068389516550638192990265 81051292137412978644742699)
            ·
              refine ⟨121576938206119467967114049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81051292137412978644742699 121576938206119467967114049)
              ·
                refine ⟨91182703654589600975335537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121576938206119467967114049 91182703654589600975335537)
                ·
                  refine ⟨68387027740942200731501653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91182703654589600975335537 68387027740942200731501653)
                  ·
                    refine ⟨801410481339166414822285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68387027740942200731501653 801410481339166414822285)
                    ·
                      rfl

theorem cell22_2341112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2341112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341112 prefixEnd_2341112 := by exact prefixLift 2341112
  have htrace : WordTrace (prefixWord ++ tailWord_2341112) baseStart_2341112 baseEnd_2341112 := by
    simpa [prefixWord, tailWord_2341112, baseEnd_2341112] using wordTrace_append hprefix tailTrace_2341112
  have hstable : (prefixWord ++ tailWord_2341112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341112).length < 2 ^ (prefixWord ++ tailWord_2341112).sum := by decide
  have hdescent : baseEnd_2341112 < baseStart_2341112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341150 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2341150 : Nat := 118140960795 + 2341150 * 2 ^ 59
def prefixEnd_2341150 : Nat := 4983230072969 + 3 ^ 40 * 2341150 * 2
def baseEnd_2341150 : Nat := 267141163171915660790723

theorem tailTrace_2341150 : CollatzResearch.WordTrace tailWord_2341150 prefixEnd_2341150 267141163171915660790723 := by
  unfold tailWord_2341150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10673594433552607679061613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56925836978947240954995269 10673594433552607679061613)
  ·
    refine ⟨4002597912582227879648105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10673594433552607679061613 4002597912582227879648105)
    ·
      refine ⟨3001948434436670909736079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4002597912582227879648105 3001948434436670909736079)
      ·
        refine ⟨4502922651655006364604119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3001948434436670909736079 4502922651655006364604119)
        ·
          refine ⟨6754383977482509546906179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4502922651655006364604119 6754383977482509546906179)
          ·
            refine ⟨10131575966223764320359269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6754383977482509546906179 10131575966223764320359269)
            ·
              refine ⟨1899670493666955810067363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10131575966223764320359269 1899670493666955810067363)
              ·
                refine ⟨2849505740500433715101045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899670493666955810067363 2849505740500433715101045)
                ·
                  refine ⟨267141163171915660790723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2849505740500433715101045 267141163171915660790723)
                  ·
                    rfl

theorem cell22_2341150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2341150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341150 prefixEnd_2341150 := by exact prefixLift 2341150
  have htrace : WordTrace (prefixWord ++ tailWord_2341150) baseStart_2341150 baseEnd_2341150 := by
    simpa [prefixWord, tailWord_2341150, baseEnd_2341150] using wordTrace_append hprefix tailTrace_2341150
  have hstable : (prefixWord ++ tailWord_2341150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341150).length < 2 ^ (prefixWord ++ tailWord_2341150).sum := by decide
  have hdescent : baseEnd_2341150 < baseStart_2341150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341219 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_2341219 : Nat := 118140960795 + 2341219 * 2 ^ 59
def prefixEnd_2341219 : Nat := 4983230072969 + 3 ^ 40 * 2341219 * 2
def baseEnd_2341219 : Nat := 801447109625853802396957

theorem tailTrace_2341219 : CollatzResearch.WordTrace tailWord_2341219 prefixEnd_2341219 801447109625853802396957 := by
  unfold tailWord_2341219
  simp only [CollatzResearch.WordTrace]
  refine ⟨85391272105170886216754711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56927514736780590811169807 85391272105170886216754711)
  ·
    refine ⟨128086908157756329325132067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85391272105170886216754711 128086908157756329325132067)
    ·
      refine ⟨192130362236634493987698101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128086908157756329325132067 192130362236634493987698101)
      ·
        refine ⟨18012221459684483811346697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192130362236634493987698101 18012221459684483811346697)
        ·
          refine ⟨13509166094763362858510023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18012221459684483811346697 13509166094763362858510023)
          ·
            refine ⟨20263749142145044287765035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509166094763362858510023 20263749142145044287765035)
            ·
              refine ⟨30395623713217566431647553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20263749142145044287765035 30395623713217566431647553)
              ·
                refine ⟨22796717784913174823735665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30395623713217566431647553 22796717784913174823735665)
                ·
                  refine ⟨17097538338684881117801749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22796717784913174823735665 17097538338684881117801749)
                  ·
                    refine ⟨801447109625853802396957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17097538338684881117801749 801447109625853802396957)
                    ·
                      rfl

theorem cell22_2341219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_2341219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341219 prefixEnd_2341219 := by exact prefixLift 2341219
  have htrace : WordTrace (prefixWord ++ tailWord_2341219) baseStart_2341219 baseEnd_2341219 := by
    simpa [prefixWord, tailWord_2341219, baseEnd_2341219] using wordTrace_append hprefix tailTrace_2341219
  have hstable : (prefixWord ++ tailWord_2341219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341219).length < 2 ^ (prefixWord ++ tailWord_2341219).sum := by decide
  have hdescent : baseEnd_2341219 < baseStart_2341219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341221 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 5, 3]
def baseStart_2341221 : Nat := 118140960795 + 2341221 * 2 ^ 59
def prefixEnd_2341221 : Nat := 4983230072969 + 3 ^ 40 * 2341221 * 2
def baseEnd_2341221 : Nat := 801447794266726463846951

theorem tailTrace_2341221 : CollatzResearch.WordTrace tailWord_2341221 prefixEnd_2341221 801447794266726463846951 := by
  unfold tailWord_2341221
  simp only [CollatzResearch.WordTrace]
  refine ⟨85391345051163640558327517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56927563367442427038885011 85391345051163640558327517)
  ·
    refine ⟨32021754394186365209372819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85391345051163640558327517 32021754394186365209372819)
    ·
      refine ⟨48032631591279547814059229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32021754394186365209372819 48032631591279547814059229)
      ·
        refine ⟨18012236846729830430272211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48032631591279547814059229 18012236846729830430272211)
        ·
          refine ⟨27018355270094745645408317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18012236846729830430272211 27018355270094745645408317)
          ·
            refine ⟨10131883226285529617028119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27018355270094745645408317 10131883226285529617028119)
            ·
              refine ⟨15197824839428294425542179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10131883226285529617028119 15197824839428294425542179)
              ·
                refine ⟨22796737259142441638313269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15197824839428294425542179 22796737259142441638313269)
                ·
                  refine ⟨2137194118044603903591869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22796737259142441638313269 2137194118044603903591869)
                  ·
                    refine ⟨801447794266726463846951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137194118044603903591869 801447794266726463846951)
                    ·
                      rfl

theorem cell22_2341221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_2341221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341221 prefixEnd_2341221 := by exact prefixLift 2341221
  have htrace : WordTrace (prefixWord ++ tailWord_2341221) baseStart_2341221 baseEnd_2341221 := by
    simpa [prefixWord, tailWord_2341221, baseEnd_2341221] using wordTrace_append hprefix tailTrace_2341221
  have hstable : (prefixWord ++ tailWord_2341221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341221).length < 2 ^ (prefixWord ++ tailWord_2341221).sum := by decide
  have hdescent : baseEnd_2341221 < baseStart_2341221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341251 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 7]
def baseStart_2341251 : Nat := 118140960795 + 2341251 * 2 ^ 59
def prefixEnd_2341251 : Nat := 4983230072969 + 3 ^ 40 * 2341251 * 2
def baseEnd_2341251 : Nat := 267152687959938795198953

theorem tailTrace_2341251 : CollatzResearch.WordTrace tailWord_2341251 prefixEnd_2341251 267152687959938795198953 := by
  unfold tailWord_2341251
  simp only [CollatzResearch.WordTrace]
  refine ⟨85392439241054955681919607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56928292827369970454613071 85392439241054955681919607)
  ·
    refine ⟨128088658861582433522879411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85392439241054955681919607 128088658861582433522879411)
    ·
      refine ⟨192132988292373650284319117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128088658861582433522879411 192132988292373650284319117)
      ·
        refine ⟨72049870609640118856619669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192132988292373650284319117 72049870609640118856619669)
        ·
          refine ⟨3377337684826880571404047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72049870609640118856619669 3377337684826880571404047)
          ·
            refine ⟨5066006527240320857106071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377337684826880571404047 5066006527240320857106071)
            ·
              refine ⟨7599009790860481285659107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066006527240320857106071 7599009790860481285659107)
              ·
                refine ⟨11398514686290721928488661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7599009790860481285659107 11398514686290721928488661)
                ·
                  refine ⟨267152687959938795198953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11398514686290721928488661 267152687959938795198953)
                  ·
                    rfl

theorem cell22_2341251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_2341251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341251 prefixEnd_2341251 := by exact prefixLift 2341251
  have htrace : WordTrace (prefixWord ++ tailWord_2341251) baseStart_2341251 baseEnd_2341251 := by
    simpa [prefixWord, tailWord_2341251, baseEnd_2341251] using wordTrace_append hprefix tailTrace_2341251
  have hstable : (prefixWord ++ tailWord_2341251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341251).length < 2 ^ (prefixWord ++ tailWord_2341251).sum := by decide
  have hdescent : baseEnd_2341251 < baseStart_2341251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341326 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2341326 : Nat := 118140960795 + 2341326 * 2 ^ 59
def prefixEnd_2341326 : Nat := 4983230072969 + 3 ^ 40 * 2341326 * 2
def baseEnd_2341326 : Nat := 801483737912541189971629

theorem tailTrace_2341326 : CollatzResearch.WordTrace tailWord_2341326 prefixEnd_2341326 801483737912541189971629 := by
  unfold tailWord_2341326
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674396839472905436362479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56930116477188828993933221 10674396839472905436362479)
  ·
    refine ⟨16011595259209358154543719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674396839472905436362479 16011595259209358154543719)
    ·
      refine ⟨24017392888814037231815579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011595259209358154543719 24017392888814037231815579)
      ·
        refine ⟨36026089333221055847723369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24017392888814037231815579 36026089333221055847723369)
        ·
          refine ⟨27019566999915791885792527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36026089333221055847723369 27019566999915791885792527)
          ·
            refine ⟨40529350499873687828688791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27019566999915791885792527 40529350499873687828688791)
            ·
              refine ⟨60794025749810531743033187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40529350499873687828688791 60794025749810531743033187)
              ·
                refine ⟨91191038624715797614549781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60794025749810531743033187 91191038624715797614549781)
                ·
                  refine ⟨4274579935533553013182021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91191038624715797614549781 4274579935533553013182021)
                  ·
                    refine ⟨801483737912541189971629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274579935533553013182021 801483737912541189971629)
                    ·
                      rfl

theorem cell22_2341326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2341326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341326 prefixEnd_2341326 := by exact prefixLift 2341326
  have htrace : WordTrace (prefixWord ++ tailWord_2341326) baseStart_2341326 baseEnd_2341326 := by
    simpa [prefixWord, tailWord_2341326, baseEnd_2341326] using wordTrace_append hprefix tailTrace_2341326
  have hstable : (prefixWord ++ tailWord_2341326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341326).length < 2 ^ (prefixWord ++ tailWord_2341326).sum := by decide
  have hdescent : baseEnd_2341326 < baseStart_2341326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341341 : List Nat := [1, 4, 3, 1, 1, 1, 1, 10]
def baseStart_2341341 : Nat := 118140960795 + 2341341 * 2 ^ 59
def prefixEnd_2341341 : Nat := 4983230072969 + 3 ^ 40 * 2341341 * 2
def baseEnd_2341341 : Nat := 89054319191009572316287

theorem tailTrace_2341341 : CollatzResearch.WordTrace tailWord_2341341 prefixEnd_2341341 89054319191009572316287 := by
  unfold tailWord_2341341
  simp only [CollatzResearch.WordTrace]
  refine ⟨85395721810728901052695877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56930481207152600701797251 85395721810728901052695877)
  ·
    refine ⟨16011697839511668947380477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85395721810728901052695877 16011697839511668947380477)
    ·
      refine ⟨6004386689816875855267679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16011697839511668947380477 6004386689816875855267679)
      ·
        refine ⟨9006580034725313782901519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004386689816875855267679 9006580034725313782901519)
        ·
          refine ⟨13509870052087970674352279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006580034725313782901519 13509870052087970674352279)
          ·
            refine ⟨20264805078131956011528419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13509870052087970674352279 20264805078131956011528419)
            ·
              refine ⟨30397207617197934017292629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20264805078131956011528419 30397207617197934017292629)
              ·
                refine ⟨89054319191009572316287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30397207617197934017292629 89054319191009572316287)
                ·
                  rfl

theorem cell22_2341341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 10].length) (baseStart_2341341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341341 prefixEnd_2341341 := by exact prefixLift 2341341
  have htrace : WordTrace (prefixWord ++ tailWord_2341341) baseStart_2341341 baseEnd_2341341 := by
    simpa [prefixWord, tailWord_2341341, baseEnd_2341341] using wordTrace_append hprefix tailTrace_2341341
  have hstable : (prefixWord ++ tailWord_2341341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341341).length < 2 ^ (prefixWord ++ tailWord_2341341).sum := by decide
  have hdescent : baseEnd_2341341 < baseStart_2341341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341343 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2341343 : Nat := 118140960795 + 2341343 * 2 ^ 59
def prefixEnd_2341343 : Nat := 4983230072969 + 3 ^ 40 * 2341343 * 2
def baseEnd_2341343 : Nat := 801489557359958812296577

theorem tailTrace_2341343 : CollatzResearch.WordTrace tailWord_2341343 prefixEnd_2341343 801489557359958812296577 := by
  unfold tailWord_2341343
  simp only [CollatzResearch.WordTrace]
  refine ⟨85395794756721655394268683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56930529837814436929512455 85395794756721655394268683)
  ·
    refine ⟨128093692135082483091403025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85395794756721655394268683 128093692135082483091403025)
    ·
      refine ⟨96070269101311862318552269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128093692135082483091403025 96070269101311862318552269)
      ·
        refine ⟨36026350912991948369457101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96070269101311862318552269 36026350912991948369457101)
        ·
          refine ⟨13509881592371980638546413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36026350912991948369457101 13509881592371980638546413)
          ·
            refine ⟨5066205597139492739454905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13509881592371980638546413 5066205597139492739454905)
            ·
              refine ⟨3799654197854619554591179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066205597139492739454905 3799654197854619554591179)
              ·
                refine ⟨5699481296781929331886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3799654197854619554591179 5699481296781929331886769)
                ·
                  refine ⟨4274610972586446998915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5699481296781929331886769 4274610972586446998915077)
                  ·
                    refine ⟨801489557359958812296577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274610972586446998915077 801489557359958812296577)
                    ·
                      rfl

theorem cell22_2341343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2341343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341343 prefixEnd_2341343 := by exact prefixLift 2341343
  have htrace : WordTrace (prefixWord ++ tailWord_2341343) baseStart_2341343 baseEnd_2341343 := by
    simpa [prefixWord, tailWord_2341343, baseEnd_2341343] using wordTrace_append hprefix tailTrace_2341343
  have hstable : (prefixWord ++ tailWord_2341343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341343).length < 2 ^ (prefixWord ++ tailWord_2341343).sum := by decide
  have hdescent : baseEnd_2341343 < baseStart_2341343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341362 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_2341362 : Nat := 118140960795 + 2341362 * 2 ^ 59
def prefixEnd_2341362 : Nat := 4983230072969 + 3 ^ 40 * 2341362 * 2
def baseEnd_2341362 : Nat := 801496061448249096071519

theorem tailTrace_2341362 : CollatzResearch.WordTrace tailWord_2341362 prefixEnd_2341362 801496061448249096071519 := by
  unfold tailWord_2341362
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349121935913205409802585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56930991829101881092806893 21349121935913205409802585)
  ·
    refine ⟨16011841451934904057351939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21349121935913205409802585 16011841451934904057351939)
    ·
      refine ⟨24017762177902356086027909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011841451934904057351939 24017762177902356086027909)
      ·
        refine ⟨4503330408356691766130233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24017762177902356086027909 4503330408356691766130233)
        ·
          refine ⟨3377497806267518824597675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4503330408356691766130233 3377497806267518824597675)
          ·
            refine ⟨5066246709401278236896513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3377497806267518824597675 5066246709401278236896513)
            ·
              refine ⟨3799685032050958677672385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066246709401278236896513 3799685032050958677672385)
              ·
                refine ⟨2849763774038219008254289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799685032050958677672385 2849763774038219008254289)
                ·
                  refine ⟨2137322830528664256190717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2849763774038219008254289 2137322830528664256190717)
                  ·
                    refine ⟨801496061448249096071519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137322830528664256190717 801496061448249096071519)
                    ·
                      rfl

theorem cell22_2341362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_2341362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341362 prefixEnd_2341362 := by exact prefixLift 2341362
  have htrace : WordTrace (prefixWord ++ tailWord_2341362) baseStart_2341362 baseEnd_2341362 := by
    simpa [prefixWord, tailWord_2341362, baseEnd_2341362] using wordTrace_append hprefix tailTrace_2341362
  have hstable : (prefixWord ++ tailWord_2341362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341362).length < 2 ^ (prefixWord ++ tailWord_2341362).sum := by decide
  have hdescent : baseEnd_2341362 < baseStart_2341362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341373 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_2341373 : Nat := 118140960795 + 2341373 * 2 ^ 59
def prefixEnd_2341373 : Nat := 4983230072969 + 3 ^ 40 * 2341373 * 2
def baseEnd_2341373 : Nat := 801499826973048734046485

theorem tailTrace_2341373 : CollatzResearch.WordTrace tailWord_2341373 prefixEnd_2341373 801499826973048734046485 := by
  unfold tailWord_2341373
  simp only [CollatzResearch.WordTrace]
  refine ⟨85396888946612970517860773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56931259297741980345240515 85396888946612970517860773)
  ·
    refine ⟨16011916677489931972098895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85396888946612970517860773 16011916677489931972098895)
    ·
      refine ⟨24017875016234897958148343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16011916677489931972098895 24017875016234897958148343)
      ·
        refine ⟨36026812524352346937222515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24017875016234897958148343 36026812524352346937222515)
        ·
          refine ⟨54040218786528520405833773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36026812524352346937222515 54040218786528520405833773)
          ·
            refine ⟨20265082044948195152187665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54040218786528520405833773 20265082044948195152187665)
            ·
              refine ⟨15198811533711146364140749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20265082044948195152187665 15198811533711146364140749)
              ·
                refine ⟨5699554325141679886552781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15198811533711146364140749 5699554325141679886552781)
                ·
                  refine ⟨2137332871928129957457293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5699554325141679886552781 2137332871928129957457293)
                  ·
                    refine ⟨801499826973048734046485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137332871928129957457293 801499826973048734046485)
                    ·
                      rfl

theorem cell22_2341373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_2341373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341373 prefixEnd_2341373 := by exact prefixLift 2341373
  have htrace : WordTrace (prefixWord ++ tailWord_2341373) baseStart_2341373 baseEnd_2341373 := by
    simpa [prefixWord, tailWord_2341373, baseEnd_2341373] using wordTrace_append hprefix tailTrace_2341373
  have hstable : (prefixWord ++ tailWord_2341373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341373).length < 2 ^ (prefixWord ++ tailWord_2341373).sum := by decide
  have hdescent : baseEnd_2341373 < baseStart_2341373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341390 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_2341390 : Nat := 118140960795 + 2341390 * 2 ^ 59
def prefixEnd_2341390 : Nat := 4983230072969 + 3 ^ 40 * 2341390 * 2
def baseEnd_2341390 : Nat := 801505646420466356371433

theorem tailTrace_2341390 : CollatzResearch.WordTrace tailWord_2341390 prefixEnd_2341390 801505646420466356371433 := by
  unfold tailWord_2341390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10674688623443922802653703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56931672658367588280819749 10674688623443922802653703)
  ·
    refine ⟨16012032935165884203980555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10674688623443922802653703 16012032935165884203980555)
    ·
      refine ⟨24018049402748826305970833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16012032935165884203980555 24018049402748826305970833)
      ·
        refine ⟨18013537052061619729478125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24018049402748826305970833 18013537052061619729478125)
        ·
          refine ⟨6755076394523107398554297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18013537052061619729478125 6755076394523107398554297)
          ·
            refine ⟨5066307295892330548915723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6755076394523107398554297 5066307295892330548915723)
            ·
              refine ⟨7599460943838495823373585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5066307295892330548915723 7599460943838495823373585)
              ·
                refine ⟨5699595707878871867530189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7599460943838495823373585 5699595707878871867530189)
                ·
                  refine ⟨2137348390454576950323821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5699595707878871867530189 2137348390454576950323821)
                  ·
                    refine ⟨801505646420466356371433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137348390454576950323821 801505646420466356371433)
                    ·
                      rfl

theorem cell22_2341390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_2341390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341390 prefixEnd_2341390 := by exact prefixLift 2341390
  have htrace : WordTrace (prefixWord ++ tailWord_2341390) baseStart_2341390 baseEnd_2341390 := by
    simpa [prefixWord, tailWord_2341390, baseEnd_2341390] using wordTrace_append hprefix tailTrace_2341390
  have hstable : (prefixWord ++ tailWord_2341390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341390).length < 2 ^ (prefixWord ++ tailWord_2341390).sum := by decide
  have hdescent : baseEnd_2341390 < baseStart_2341390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341418 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2341418 : Nat := 118140960795 + 2341418 * 2 ^ 59
def prefixEnd_2341418 : Nat := 4983230072969 + 3 ^ 40 * 2341418 * 2
def baseEnd_2341418 : Nat := 801515231392683616671347

theorem tailTrace_2341418 : CollatzResearch.WordTrace tailWord_2341418 prefixEnd_2341418 801515231392683616671347 := by
  unfold tailWord_2341418
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349632557862485800812227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56932353487633295468832605 21349632557862485800812227)
  ·
    refine ⟨32024448836793728701218341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21349632557862485800812227 32024448836793728701218341)
    ·
      refine ⟨6004584156898824131478439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32024448836793728701218341 6004584156898824131478439)
      ·
        refine ⟨9006876235348236197217659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004584156898824131478439 9006876235348236197217659)
        ·
          refine ⟨13510314353022354295826489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9006876235348236197217659 13510314353022354295826489)
          ·
            refine ⟨10132735764766765721869867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13510314353022354295826489 10132735764766765721869867)
            ·
              refine ⟨15199103647150148582804801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10132735764766765721869867 15199103647150148582804801)
              ·
                refine ⟨11399327735362611437103601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15199103647150148582804801 11399327735362611437103601)
                ·
                  refine ⟨8549495801521958577827701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11399327735362611437103601 8549495801521958577827701)
                  ·
                    refine ⟨801515231392683616671347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8549495801521958577827701 801515231392683616671347)
                    ·
                      rfl

theorem cell22_2341418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2341418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341418 prefixEnd_2341418 := by exact prefixLift 2341418
  have htrace : WordTrace (prefixWord ++ tailWord_2341418) baseStart_2341418 baseEnd_2341418 := by
    simpa [prefixWord, tailWord_2341418, baseEnd_2341418] using wordTrace_append hprefix tailTrace_2341418
  have hstable : (prefixWord ++ tailWord_2341418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341418).length < 2 ^ (prefixWord ++ tailWord_2341418).sum := by decide
  have hdescent : baseEnd_2341418 < baseStart_2341418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341450 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2341450 : Nat := 118140960795 + 2341450 * 2 ^ 59
def prefixEnd_2341450 : Nat := 4983230072969 + 3 ^ 40 * 2341450 * 2
def baseEnd_2341450 : Nat := 801526185646646199871249

theorem tailTrace_2341450 : CollatzResearch.WordTrace tailWord_2341450 prefixEnd_2341450 801526185646646199871249 := by
  unfold tailWord_2341450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21349924341833503167103451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56933131578222675112275869 21349924341833503167103451)
  ·
    refine ⟨32024886512750254750655177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21349924341833503167103451 32024886512750254750655177)
    ·
      refine ⟨24018664884562691062991383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32024886512750254750655177 24018664884562691062991383)
      ·
        refine ⟨36027997326844036594487075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24018664884562691062991383 36027997326844036594487075)
        ·
          refine ⟨54041995990266054891730613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36027997326844036594487075 54041995990266054891730613)
          ·
            refine ⟨5066437124087442646099745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54041995990266054891730613 5066437124087442646099745)
            ·
              refine ⟨3799827843065581984574809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5066437124087442646099745 3799827843065581984574809)
              ·
                refine ⟨2849870882299186488431107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3799827843065581984574809 2849870882299186488431107)
                ·
                  refine ⟨4274806323448779732646661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2849870882299186488431107 4274806323448779732646661)
                  ·
                    refine ⟨801526185646646199871249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4274806323448779732646661 801526185646646199871249)
                    ·
                      rfl

theorem cell22_2341450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2341450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341450 prefixEnd_2341450 := by exact prefixLift 2341450
  have htrace : WordTrace (prefixWord ++ tailWord_2341450) baseStart_2341450 baseEnd_2341450 := by
    simpa [prefixWord, tailWord_2341450, baseEnd_2341450] using wordTrace_append hprefix tailTrace_2341450
  have hstable : (prefixWord ++ tailWord_2341450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341450).length < 2 ^ (prefixWord ++ tailWord_2341450).sum := by decide
  have hdescent : baseEnd_2341450 < baseStart_2341450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341463 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 6, 3]
def baseStart_2341463 : Nat := 118140960795 + 2341463 * 2 ^ 59
def prefixEnd_2341463 : Nat := 4983230072969 + 3 ^ 40 * 2341463 * 2
def baseEnd_2341463 : Nat := 801530635812318499296209

theorem tailTrace_2341463 : CollatzResearch.WordTrace tailWord_2341463 prefixEnd_2341463 801530635812318499296209 := by
  unfold tailWord_2341463
  simp only [CollatzResearch.WordTrace]
  refine ⟨85400171516286915888637043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56933447677524610592424695 85400171516286915888637043)
  ·
    refine ⟨128100257274430373832955565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85400171516286915888637043 128100257274430373832955565)
    ·
      refine ⟨48037596477911390187358337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128100257274430373832955565 48037596477911390187358337)
      ·
        refine ⟨36028197358433542640518753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48037596477911390187358337 36028197358433542640518753)
        ·
          refine ⟨27021148018825156980389065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36028197358433542640518753 27021148018825156980389065)
          ·
            refine ⟨20265861014118867735291799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27021148018825156980389065 20265861014118867735291799)
            ·
              refine ⟨30398791521178301602937699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20265861014118867735291799 30398791521178301602937699)
              ·
                refine ⟨45598187281767452404406549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30398791521178301602937699 45598187281767452404406549)
                ·
                  refine ⟨2137415028832849331456557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45598187281767452404406549 2137415028832849331456557)
                  ·
                    refine ⟨801530635812318499296209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137415028832849331456557 801530635812318499296209)
                    ·
                      rfl

theorem cell22_2341463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_2341463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341463 prefixEnd_2341463 := by exact prefixLift 2341463
  have htrace : WordTrace (prefixWord ++ tailWord_2341463) baseStart_2341463 baseEnd_2341463 := by
    simpa [prefixWord, tailWord_2341463, baseEnd_2341463] using wordTrace_append hprefix tailTrace_2341463
  have hstable : (prefixWord ++ tailWord_2341463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341463).length < 2 ^ (prefixWord ++ tailWord_2341463).sum := by decide
  have hdescent : baseEnd_2341463 < baseStart_2341463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341482 : List Nat := [3, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_2341482 : Nat := 118140960795 + 2341482 * 2 ^ 59
def prefixEnd_2341482 : Nat := 4983230072969 + 3 ^ 40 * 2341482 * 2
def baseEnd_2341482 : Nat := 267179046633536261023717

theorem tailTrace_2341482 : CollatzResearch.WordTrace tailWord_2341482 prefixEnd_2341482 267179046633536261023717 := by
  unfold tailWord_2341482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21350216125804520533394675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56933909668812054755719133 21350216125804520533394675)
  ·
    refine ⟨32025324188706780800092013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21350216125804520533394675 32025324188706780800092013)
    ·
      refine ⟨12009496570765042800034505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32025324188706780800092013 12009496570765042800034505)
      ·
        refine ⟨9007122428073782100025879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12009496570765042800034505 9007122428073782100025879)
        ·
          refine ⟨13510683642110673150038819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9007122428073782100025879 13510683642110673150038819)
          ·
            refine ⟨20266025463166009725058229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13510683642110673150038819 20266025463166009725058229)
            ·
              refine ⟨1899939887171813411724209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20266025463166009725058229 1899939887171813411724209)
              ·
                refine ⟨1424954915378860058793157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899939887171813411724209 1424954915378860058793157)
                ·
                  refine ⟨267179046633536261023717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1424954915378860058793157 267179046633536261023717)
                  ·
                    rfl

theorem cell22_2341482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_2341482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341482 prefixEnd_2341482 := by exact prefixLift 2341482
  have htrace : WordTrace (prefixWord ++ tailWord_2341482) baseStart_2341482 baseEnd_2341482 := by
    simpa [prefixWord, tailWord_2341482, baseEnd_2341482] using wordTrace_append hprefix tailTrace_2341482
  have hstable : (prefixWord ++ tailWord_2341482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341482).length < 2 ^ (prefixWord ++ tailWord_2341482).sum := by decide
  have hdescent : baseEnd_2341482 < baseStart_2341482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341491 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_2341491 : Nat := 118140960795 + 2341491 * 2 ^ 59
def prefixEnd_2341491 : Nat := 4983230072969 + 3 ^ 40 * 2341491 * 2
def baseEnd_2341491 : Nat := 801540220784535759596123

theorem tailTrace_2341491 : CollatzResearch.WordTrace tailWord_2341491 prefixEnd_2341491 801540220784535759596123 := by
  unfold tailWord_2341491
  simp only [CollatzResearch.WordTrace]
  refine ⟨85401192760185476670656327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56934128506790317780437551 85401192760185476670656327)
  ·
    refine ⟨128101789140278215005984491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85401192760185476670656327 128101789140278215005984491)
    ·
      refine ⟨192152683710417322508976737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128101789140278215005984491 192152683710417322508976737)
      ·
        refine ⟨144114512782812991881732553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192152683710417322508976737 144114512782812991881732553)
        ·
          refine ⟨108085884587109743911299415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144114512782812991881732553 108085884587109743911299415)
          ·
            refine ⟨162128826880664615866949123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108085884587109743911299415 162128826880664615866949123)
            ·
              refine ⟨243193240320996923800423685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162128826880664615866949123 243193240320996923800423685)
              ·
                refine ⟨45598732560186923212579441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243193240320996923800423685 45598732560186923212579441)
                ·
                  refine ⟨34199049420140192409434581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45598732560186923212579441 34199049420140192409434581)
                  ·
                    refine ⟨801540220784535759596123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34199049420140192409434581 801540220784535759596123)
                    ·
                      rfl

theorem cell22_2341491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_2341491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341491 prefixEnd_2341491 := by exact prefixLift 2341491
  have htrace : WordTrace (prefixWord ++ tailWord_2341491) baseStart_2341491 baseEnd_2341491 := by
    simpa [prefixWord, tailWord_2341491, baseEnd_2341491] using wordTrace_append hprefix tailTrace_2341491
  have hstable : (prefixWord ++ tailWord_2341491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341491).length < 2 ^ (prefixWord ++ tailWord_2341491).sum := by decide
  have hdescent : baseEnd_2341491 < baseStart_2341491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341497 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 2, 3]
def baseStart_2341497 : Nat := 118140960795 + 2341497 * 2 ^ 59
def prefixEnd_2341497 : Nat := 4983230072969 + 3 ^ 40 * 2341497 * 2
def baseEnd_2341497 : Nat := 801542274707153743946105

theorem tailTrace_2341497 : CollatzResearch.WordTrace tailWord_2341497 prefixEnd_2341497 801542274707153743946105 := by
  unfold tailWord_2341497
  simp only [CollatzResearch.WordTrace]
  refine ⟨85401411598163739695374745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56934274398775826463583163 85401411598163739695374745)
  ·
    refine ⟨64051058698622804771531059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85401411598163739695374745 64051058698622804771531059)
    ·
      refine ⟨96076588047934207157296589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64051058698622804771531059 96076588047934207157296589)
      ·
        refine ⟨36028720517975327683986221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96076588047934207157296589 36028720517975327683986221)
        ·
          refine ⟨13510770194240747881494833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36028720517975327683986221 13510770194240747881494833)
          ·
            refine ⟨10133077645680560911121125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13510770194240747881494833 10133077645680560911121125)
            ·
              refine ⟨1899952058565105170835211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10133077645680560911121125 1899952058565105170835211)
              ·
                refine ⟨2849928087847657756252817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1899952058565105170835211 2849928087847657756252817)
                ·
                  refine ⟨2137446065885743317189613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2849928087847657756252817 2137446065885743317189613)
                  ·
                    refine ⟨801542274707153743946105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137446065885743317189613 801542274707153743946105)
                    ·
                      rfl

theorem cell22_2341497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_2341497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341497 prefixEnd_2341497 := by exact prefixLift 2341497
  have htrace : WordTrace (prefixWord ++ tailWord_2341497) baseStart_2341497 baseEnd_2341497 := by
    simpa [prefixWord, tailWord_2341497, baseEnd_2341497] using wordTrace_append hprefix tailTrace_2341497
  have hstable : (prefixWord ++ tailWord_2341497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341497).length < 2 ^ (prefixWord ++ tailWord_2341497).sum := by decide
  have hdescent : baseEnd_2341497 < baseStart_2341497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341585 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2341585 : Nat := 118140960795 + 2341585 * 2 ^ 59
def prefixEnd_2341585 : Nat := 4983230072969 + 3 ^ 40 * 2341585 * 2
def baseEnd_2341585 : Nat := 801572398905550847745835

theorem tailTrace_2341585 : CollatzResearch.WordTrace tailWord_2341585 prefixEnd_2341585 801572398905550847745835 := by
  unfold tailWord_2341585
  simp only [CollatzResearch.WordTrace]
  refine ⟨85404621221844930724578209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56936414147896620483052139 85404621221844930724578209)
  ·
    refine ⟨64053465916383698043433657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85404621221844930724578209 64053465916383698043433657)
    ·
      refine ⟨48040099437287773532575243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64053465916383698043433657 48040099437287773532575243)
      ·
        refine ⟨72060149155931660298862865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48040099437287773532575243 72060149155931660298862865)
        ·
          refine ⟨54045111866948745224147149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72060149155931660298862865 54045111866948745224147149)
          ·
            refine ⟨20266916950105779459055181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54045111866948745224147149 20266916950105779459055181)
            ·
              refine ⟨7600093856289667297145693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20266916950105779459055181 7600093856289667297145693)
              ·
                refine ⟨2850035196108625236429635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7600093856289667297145693 2850035196108625236429635)
                ·
                  refine ⟨4275052794162937854644453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850035196108625236429635 4275052794162937854644453)
                  ·
                    refine ⟨801572398905550847745835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275052794162937854644453 801572398905550847745835)
                    ·
                      rfl

theorem cell22_2341585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2341585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341585 prefixEnd_2341585 := by exact prefixLift 2341585
  have htrace : WordTrace (prefixWord ++ tailWord_2341585) baseStart_2341585 baseEnd_2341585 := by
    simpa [prefixWord, tailWord_2341585, baseEnd_2341585] using wordTrace_append hprefix tailTrace_2341585
  have hstable : (prefixWord ++ tailWord_2341585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341585).length < 2 ^ (prefixWord ++ tailWord_2341585).sum := by decide
  have hdescent : baseEnd_2341585 < baseStart_2341585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341589 : List Nat := [1, 3, 2, 5, 1, 2, 1, 2, 5]
def baseStart_2341589 : Nat := 118140960795 + 2341589 * 2 ^ 59
def prefixEnd_2341589 : Nat := 4983230072969 + 3 ^ 40 * 2341589 * 2
def baseEnd_2341589 : Nat := 267191256062432056881941

theorem tailTrace_2341589 : CollatzResearch.WordTrace tailWord_2341589 prefixEnd_2341589 267191256062432056881941 := by
  unfold tailWord_2341589
  simp only [CollatzResearch.WordTrace]
  refine ⟨85404767113830439407723821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56936511409220292938482547 85404767113830439407723821)
  ·
    refine ⟨32026787667686414777896433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85404767113830439407723821 32026787667686414777896433)
    ·
      refine ⟨24020090750764811083422325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32026787667686414777896433 24020090750764811083422325)
      ·
        refine ⟨2251883507884201039070843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24020090750764811083422325 2251883507884201039070843)
        ·
          refine ⟨3377825261826301558606265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2251883507884201039070843 3377825261826301558606265)
          ·
            refine ⟨2533368946369726168954699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3377825261826301558606265 2533368946369726168954699)
            ·
              refine ⟨3800053419554589253432049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533368946369726168954699 3800053419554589253432049)
              ·
                refine ⟨2850040064665941940074037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3800053419554589253432049 2850040064665941940074037)
                ·
                  refine ⟨267191256062432056881941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850040064665941940074037 267191256062432056881941)
                  ·
                    rfl

theorem cell22_2341589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_2341589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341589 prefixEnd_2341589 := by exact prefixLift 2341589
  have htrace : WordTrace (prefixWord ++ tailWord_2341589) baseStart_2341589 baseEnd_2341589 := by
    simpa [prefixWord, tailWord_2341589, baseEnd_2341589] using wordTrace_append hprefix tailTrace_2341589
  have hstable : (prefixWord ++ tailWord_2341589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341589).length < 2 ^ (prefixWord ++ tailWord_2341589).sum := by decide
  have hdescent : baseEnd_2341589 < baseStart_2341589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341615 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2341615 : Nat := 118140960795 + 2341615 * 2 ^ 59
def prefixEnd_2341615 : Nat := 4983230072969 + 3 ^ 40 * 2341615 * 2
def baseEnd_2341615 : Nat := 801582668518640769495743

theorem tailTrace_2341615 : CollatzResearch.WordTrace tailWord_2341615 prefixEnd_2341615 801582668518640769495743 := by
  unfold tailWord_2341615
  simp only [CollatzResearch.WordTrace]
  refine ⟨85405715411736245848170299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56937143607824163898780199 85405715411736245848170299)
  ·
    refine ⟨128108573117604368772255449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85405715411736245848170299 128108573117604368772255449)
    ·
      refine ⟨96081429838203276579191587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128108573117604368772255449 96081429838203276579191587)
      ·
        refine ⟨144122144757304914868787381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96081429838203276579191587 144122144757304914868787381)
        ·
          refine ⟨13511451070997335768948817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144122144757304914868787381 13511451070997335768948817)
          ·
            refine ⟨10133588303248001826711613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13511451070997335768948817 10133588303248001826711613)
            ·
              refine ⟨3800095613718000685016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10133588303248001826711613 3800095613718000685016855)
              ·
                refine ⟨5700143420577001027525283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800095613718000685016855 5700143420577001027525283)
                ·
                  refine ⟨8550215130865501541287925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700143420577001027525283 8550215130865501541287925)
                  ·
                    refine ⟨801582668518640769495743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8550215130865501541287925 801582668518640769495743)
                    ·
                      rfl

theorem cell22_2341615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2341615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341615 prefixEnd_2341615 := by exact prefixLift 2341615
  have htrace : WordTrace (prefixWord ++ tailWord_2341615) baseStart_2341615 baseEnd_2341615 := by
    simpa [prefixWord, tailWord_2341615, baseEnd_2341615] using wordTrace_append hprefix tailTrace_2341615
  have hstable : (prefixWord ++ tailWord_2341615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341615).length < 2 ^ (prefixWord ++ tailWord_2341615).sum := by decide
  have hdescent : baseEnd_2341615 < baseStart_2341615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341634 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2341634 : Nat := 118140960795 + 2341634 * 2 ^ 59
def prefixEnd_2341634 : Nat := 4983230072969 + 3 ^ 40 * 2341634 * 2
def baseEnd_2341634 : Nat := 267196390868977017756895

theorem tailTrace_2341634 : CollatzResearch.WordTrace tailWord_2341634 prefixEnd_2341634 267196390868977017756895 := by
  unfold tailWord_2341634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21351602099666853023277989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56937605599111608062074637 21351602099666853023277989)
  ·
    refine ⟨4003425393687534941864623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21351602099666853023277989 4003425393687534941864623)
    ·
      refine ⟨6005138090531302412796935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003425393687534941864623 6005138090531302412796935)
      ·
        refine ⟨9007707135796953619195403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005138090531302412796935 9007707135796953619195403)
        ·
          refine ⟨13511560703695430428793105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9007707135796953619195403 13511560703695430428793105)
          ·
            refine ⟨10133670527771572821594829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13511560703695430428793105 10133670527771572821594829)
            ·
              refine ⟨3800126447914339808098061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10133670527771572821594829 3800126447914339808098061)
              ·
                refine ⟨1425047417967877428036773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3800126447914339808098061 1425047417967877428036773)
                ·
                  refine ⟨267196390868977017756895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425047417967877428036773 267196390868977017756895)
                  ·
                    rfl

theorem cell22_2341634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2341634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341634 prefixEnd_2341634 := by exact prefixLift 2341634
  have htrace : WordTrace (prefixWord ++ tailWord_2341634) baseStart_2341634 baseEnd_2341634 := by
    simpa [prefixWord, tailWord_2341634, baseEnd_2341634] using wordTrace_append hprefix tailTrace_2341634
  have hstable : (prefixWord ++ tailWord_2341634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341634).length < 2 ^ (prefixWord ++ tailWord_2341634).sum := by decide
  have hdescent : baseEnd_2341634 < baseStart_2341634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341666 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2341666 : Nat := 118140960795 + 2341666 * 2 ^ 59
def prefixEnd_2341666 : Nat := 4983230072969 + 3 ^ 40 * 2341666 * 2
def baseEnd_2341666 : Nat := 801600126860893636470587

theorem tailTrace_2341666 : CollatzResearch.WordTrace tailWord_2341666 prefixEnd_2341666 801600126860893636470587 := by
  unfold tailWord_2341666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21351893883637870389569213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56938383689700987705517901 21351893883637870389569213)
  ·
    refine ⟨8006960206364201396088455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21351893883637870389569213 8006960206364201396088455)
    ·
      refine ⟨12010440309546302094132683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8006960206364201396088455 12010440309546302094132683)
      ·
        refine ⟨18015660464319453141199025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010440309546302094132683 18015660464319453141199025)
        ·
          refine ⟨13511745348239589855899269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18015660464319453141199025 13511745348239589855899269)
          ·
            refine ⟨2533452252794923097981113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13511745348239589855899269 2533452252794923097981113)
            ·
              refine ⟨1900089189596192323485835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533452252794923097981113 1900089189596192323485835)
              ·
                refine ⟨2850133784394288485228753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900089189596192323485835 2850133784394288485228753)
                ·
                  refine ⟨2137600338295716363921565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850133784394288485228753 2137600338295716363921565)
                  ·
                    refine ⟨801600126860893636470587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137600338295716363921565 801600126860893636470587)
                    ·
                      rfl

theorem cell22_2341666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2341666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341666 prefixEnd_2341666 := by exact prefixLift 2341666
  have htrace : WordTrace (prefixWord ++ tailWord_2341666) baseStart_2341666 baseEnd_2341666 := by
    simpa [prefixWord, tailWord_2341666, baseEnd_2341666] using wordTrace_append hprefix tailTrace_2341666
  have hstable : (prefixWord ++ tailWord_2341666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341666).length < 2 ^ (prefixWord ++ tailWord_2341666).sum := by decide
  have hdescent : baseEnd_2341666 < baseStart_2341666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341735 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 8]
def baseStart_2341735 : Nat := 118140960795 + 2341735 * 2 ^ 59
def prefixEnd_2341735 : Nat := 4983230072969 + 3 ^ 40 * 2341735 * 2
def baseEnd_2341735 : Nat := 267207915657000152165125

theorem tailTrace_2341735 : CollatzResearch.WordTrace tailWord_2341735 prefixEnd_2341735 267207915657000152165125 := by
  unfold tailWord_2341735
  simp only [CollatzResearch.WordTrace]
  refine ⟨85410092171301506342538659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56940061447534337561692439 85410092171301506342538659)
  ·
    refine ⟨128115138256952259513807989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85410092171301506342538659 128115138256952259513807989)
    ·
      refine ⟨12010794211589274329419499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128115138256952259513807989 12010794211589274329419499)
      ·
        refine ⟨18016191317383911494129249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010794211589274329419499 18016191317383911494129249)
        ·
          refine ⟨13512143488037933620596937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18016191317383911494129249 13512143488037933620596937)
          ·
            refine ⟨10134107616028450215447703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13512143488037933620596937 10134107616028450215447703)
            ·
              refine ⟨15201161424042675323171555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10134107616028450215447703 15201161424042675323171555)
              ·
                refine ⟨22801742136064012984757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15201161424042675323171555 22801742136064012984757333)
                ·
                  refine ⟨267207915657000152165125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22801742136064012984757333 267207915657000152165125)
                  ·
                    rfl

theorem cell22_2341735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_2341735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341735 prefixEnd_2341735 := by exact prefixLift 2341735
  have htrace : WordTrace (prefixWord ++ tailWord_2341735) baseStart_2341735 baseEnd_2341735 := by
    simpa [prefixWord, tailWord_2341735, baseEnd_2341735] using wordTrace_append hprefix tailTrace_2341735
  have hstable : (prefixWord ++ tailWord_2341735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341735).length < 2 ^ (prefixWord ++ tailWord_2341735).sum := by decide
  have hdescent : baseEnd_2341735 < baseStart_2341735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341758 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_2341758 : Nat := 118140960795 + 2341758 * 2 ^ 59
def prefixEnd_2341758 : Nat := 4983230072969 + 3 ^ 40 * 2341758 * 2
def baseEnd_2341758 : Nat := 267210540113678687723435

theorem tailTrace_2341758 : CollatzResearch.WordTrace tailWord_2341758 prefixEnd_2341758 267210540113678687723435 := by
  unfold tailWord_2341758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10676366381277272658828241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56940620700145454180417285 10676366381277272658828241)
  ·
    refine ⟨8007274785957954494121181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10676366381277272658828241 8007274785957954494121181)
    ·
      refine ⟨3002728044734232935295443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8007274785957954494121181 3002728044734232935295443)
      ·
        refine ⟨4504092067101349402943165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002728044734232935295443 4504092067101349402943165)
        ·
          refine ⟨1689034525163006026103687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4504092067101349402943165 1689034525163006026103687)
          ·
            refine ⟨2533551787744509039155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689034525163006026103687 2533551787744509039155531)
            ·
              refine ⟨3800327681616763558733297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533551787744509039155531 3800327681616763558733297)
              ·
                refine ⟨2850245761212572669049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3800327681616763558733297 2850245761212572669049973)
                ·
                  refine ⟨267210540113678687723435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2850245761212572669049973 267210540113678687723435)
                  ·
                    rfl

theorem cell22_2341758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_2341758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341758 prefixEnd_2341758 := by exact prefixLift 2341758
  have htrace : WordTrace (prefixWord ++ tailWord_2341758) baseStart_2341758 baseEnd_2341758 := by
    simpa [prefixWord, tailWord_2341758, baseEnd_2341758] using wordTrace_append hprefix tailTrace_2341758
  have hstable : (prefixWord ++ tailWord_2341758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341758).length < 2 ^ (prefixWord ++ tailWord_2341758).sum := by decide
  have hdescent : baseEnd_2341758 < baseStart_2341758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341810 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2341810 : Nat := 118140960795 + 2341810 * 2 ^ 59
def prefixEnd_2341810 : Nat := 4983230072969 + 3 ^ 40 * 2341810 * 2
def baseEnd_2341810 : Nat := 801649421003725260870145

theorem tailTrace_2341810 : CollatzResearch.WordTrace tailWord_2341810 prefixEnd_2341810 801649421003725260870145 := by
  unfold tailWord_2341810
  simp only [CollatzResearch.WordTrace]
  refine ⟨21353206911507448537879721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56941885097353196101012589 21353206911507448537879721)
  ·
    refine ⟨16014905183630586403409791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21353206911507448537879721 16014905183630586403409791)
    ·
      refine ⟨24022357775445879605114687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16014905183630586403409791 24022357775445879605114687)
      ·
        refine ⟨36033536663168819407672031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24022357775445879605114687 36033536663168819407672031)
        ·
          refine ⟨54050304994753229111508047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36033536663168819407672031 54050304994753229111508047)
          ·
            refine ⟨81075457492129843667262071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54050304994753229111508047 81075457492129843667262071)
            ·
              refine ⟨121613186238194765500893107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81075457492129843667262071 121613186238194765500893107)
              ·
                refine ⟨182419779357292148251339661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121613186238194765500893107 182419779357292148251339661)
                ·
                  refine ⟨68407417258984555594252373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182419779357292148251339661 68407417258984555594252373)
                  ·
                    refine ⟨801649421003725260870145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68407417258984555594252373 801649421003725260870145)
                    ·
                      rfl

theorem cell22_2341810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2341810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341810 prefixEnd_2341810 := by exact prefixLift 2341810
  have htrace : WordTrace (prefixWord ++ tailWord_2341810) baseStart_2341810 baseEnd_2341810 := by
    simpa [prefixWord, tailWord_2341810, baseEnd_2341810] using wordTrace_append hprefix tailTrace_2341810
  have hstable : (prefixWord ++ tailWord_2341810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341810).length < 2 ^ (prefixWord ++ tailWord_2341810).sum := by decide
  have hdescent : baseEnd_2341810 < baseStart_2341810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341840 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_2341840 : Nat := 118140960795 + 2341840 * 2 ^ 59
def prefixEnd_2341840 : Nat := 4983230072969 + 3 ^ 40 * 2341840 * 2
def baseEnd_2341840 : Nat := 801659690616815182620053

theorem tailTrace_2341840 : CollatzResearch.WordTrace tailWord_2341840 prefixEnd_2341840 801659690616815182620053 := by
  unfold tailWord_2341840
  simp only [CollatzResearch.WordTrace]
  refine ⟨42706960917960554637555487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56942614557280739516740649 42706960917960554637555487)
  ·
    refine ⟨64060441376940831956333231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42706960917960554637555487 64060441376940831956333231)
    ·
      refine ⟨96090662065411247934499847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64060441376940831956333231 96090662065411247934499847)
      ·
        refine ⟨144135993098116871901749771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96090662065411247934499847 144135993098116871901749771)
        ·
          refine ⟨216203989647175307852624657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144135993098116871901749771 216203989647175307852624657)
          ·
            refine ⟨162152992235381480889468493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216203989647175307852624657 162152992235381480889468493)
            ·
              refine ⟨60807372088268055333550685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162152992235381480889468493 60807372088268055333550685)
              ·
                refine ⟨22802764533100520750081507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60807372088268055333550685 22802764533100520750081507)
                ·
                  refine ⟨34204146799650781125122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22802764533100520750081507 34204146799650781125122261)
                  ·
                    refine ⟨801659690616815182620053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34204146799650781125122261 801659690616815182620053)
                    ·
                      rfl

theorem cell22_2341840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_2341840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341840 prefixEnd_2341840 := by exact prefixLift 2341840
  have htrace : WordTrace (prefixWord ++ tailWord_2341840) baseStart_2341840 baseEnd_2341840 := by
    simpa [prefixWord, tailWord_2341840, baseEnd_2341840] using wordTrace_append hprefix tailTrace_2341840
  have hstable : (prefixWord ++ tailWord_2341840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341840).length < 2 ^ (prefixWord ++ tailWord_2341840).sum := by decide
  have hdescent : baseEnd_2341840 < baseStart_2341840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341921 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 4]
def baseStart_2341921 : Nat := 118140960795 + 2341921 * 2 ^ 59
def prefixEnd_2341921 : Nat := 4983230072969 + 3 ^ 40 * 2341921 * 2
def baseEnd_2341921 : Nat := 267229139524052657114935

theorem tailTrace_2341921 : CollatzResearch.WordTrace tailWord_2341921 prefixEnd_2341921 267229139524052657114935 := by
  unfold tailWord_2341921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85416876148627660108809617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56944584099085106739206411 85416876148627660108809617)
  ·
    refine ⟨64062657111470745081607213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85416876148627660108809617 64062657111470745081607213)
    ·
      refine ⟨24023496416801529405602705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64062657111470745081607213 24023496416801529405602705)
      ·
        refine ⟨18017622312601147054202029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24023496416801529405602705 18017622312601147054202029)
        ·
          refine ⟨6756608367225430145325761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18017622312601147054202029 6756608367225430145325761)
          ·
            refine ⟨5067456275419072608994321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6756608367225430145325761 5067456275419072608994321)
            ·
              refine ⟨3800592206564304456745741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5067456275419072608994321 3800592206564304456745741)
              ·
                refine ⟨1425222077461614171279653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3800592206564304456745741 1425222077461614171279653)
                ·
                  refine ⟨267229139524052657114935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1425222077461614171279653 267229139524052657114935)
                  ·
                    rfl

theorem cell22_2341921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_2341921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341921 prefixEnd_2341921 := by exact prefixLift 2341921
  have htrace : WordTrace (prefixWord ++ tailWord_2341921) baseStart_2341921 baseEnd_2341921 := by
    simpa [prefixWord, tailWord_2341921, baseEnd_2341921] using wordTrace_append hprefix tailTrace_2341921
  have hstable : (prefixWord ++ tailWord_2341921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341921).length < 2 ^ (prefixWord ++ tailWord_2341921).sum := by decide
  have hdescent : baseEnd_2341921 < baseStart_2341921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341934 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2341934 : Nat := 118140960795 + 2341934 * 2 ^ 59
def prefixEnd_2341934 : Nat := 4983230072969 + 3 ^ 40 * 2341934 * 2
def baseEnd_2341934 : Nat := 801691868737830270769765

theorem tailTrace_2341934 : CollatzResearch.WordTrace tailWord_2341934 prefixEnd_2341934 801691868737830270769765 := by
  unfold tailWord_2341934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677168787197570416129107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56944900198387042219355237 10677168787197570416129107)
  ·
    refine ⟨16015753180796355624193661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10677168787197570416129107 16015753180796355624193661)
    ·
      refine ⟨6005907442798633359072623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16015753180796355624193661 6005907442798633359072623)
      ·
        refine ⟨9008861164197950038608935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005907442798633359072623 9008861164197950038608935)
        ·
          refine ⟨13513291746296925057913403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9008861164197950038608935 13513291746296925057913403)
          ·
            refine ⟨20269937619445387586870105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13513291746296925057913403 20269937619445387586870105)
            ·
              refine ⟨15202453214584040690152579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20269937619445387586870105 15202453214584040690152579)
              ·
                refine ⟨22803679821876061035228869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15202453214584040690152579 22803679821876061035228869)
                ·
                  refine ⟨4275689966601761444105413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22803679821876061035228869 4275689966601761444105413)
                  ·
                    refine ⟨801691868737830270769765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4275689966601761444105413 801691868737830270769765)
                    ·
                      rfl

theorem cell22_2341934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2341934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341934 prefixEnd_2341934 := by exact prefixLift 2341934
  have htrace : WordTrace (prefixWord ++ tailWord_2341934) baseStart_2341934 baseEnd_2341934 := by
    simpa [prefixWord, tailWord_2341934, baseEnd_2341934] using wordTrace_append hprefix tailTrace_2341934
  have hstable : (prefixWord ++ tailWord_2341934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341934).length < 2 ^ (prefixWord ++ tailWord_2341934).sum := by decide
  have hdescent : baseEnd_2341934 < baseStart_2341934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341953 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2341953 : Nat := 118140960795 + 2341953 * 2 ^ 59
def prefixEnd_2341953 : Nat := 4983230072969 + 3 ^ 40 * 2341953 * 2
def baseEnd_2341953 : Nat := 801698372826120554544707

theorem tailTrace_2341953 : CollatzResearch.WordTrace tailWord_2341953 prefixEnd_2341953 801698372826120554544707 := by
  unfold tailWord_2341953
  simp only [CollatzResearch.WordTrace]
  refine ⟨85418043284511729573974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56945362189674486382649675 85418043284511729573974513)
  ·
    refine ⟨64063532463383797180480885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85418043284511729573974513 64063532463383797180480885)
    ·
      refine ⟨6005956168442230985670083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64063532463383797180480885 6005956168442230985670083)
      ·
        refine ⟨9008934252663346478505125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005956168442230985670083 9008934252663346478505125)
        ·
          refine ⟨1689175172374377464719711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9008934252663346478505125 1689175172374377464719711)
          ·
            refine ⟨2533762758561566197079567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689175172374377464719711 2533762758561566197079567)
            ·
              refine ⟨3800644137842349295619351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533762758561566197079567 3800644137842349295619351)
              ·
                refine ⟨5700966206763523943429027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800644137842349295619351 5700966206763523943429027)
                ·
                  refine ⟨8551449310145285915143541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5700966206763523943429027 8551449310145285915143541)
                  ·
                    refine ⟨801698372826120554544707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8551449310145285915143541 801698372826120554544707)
                    ·
                      rfl

theorem cell22_2341953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2341953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341953 prefixEnd_2341953 := by exact prefixLift 2341953
  have htrace : WordTrace (prefixWord ++ tailWord_2341953) baseStart_2341953 baseEnd_2341953 := by
    simpa [prefixWord, tailWord_2341953, baseEnd_2341953] using wordTrace_append hprefix tailTrace_2341953
  have hstable : (prefixWord ++ tailWord_2341953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341953).length < 2 ^ (prefixWord ++ tailWord_2341953).sum := by decide
  have hdescent : baseEnd_2341953 < baseStart_2341953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341962 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2341962 : Nat := 118140960795 + 2341962 * 2 ^ 59
def prefixEnd_2341962 : Nat := 4983230072969 + 3 ^ 40 * 2341962 * 2
def baseEnd_2341962 : Nat := 801701453710047531069679

theorem tailTrace_2341962 : CollatzResearch.WordTrace tailWord_2341962 prefixEnd_2341962 801701453710047531069679 := by
  unfold tailWord_2341962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354592885369781027763035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56945581027652749407368093 21354592885369781027763035)
  ·
    refine ⟨32031889328054671541644553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21354592885369781027763035 32031889328054671541644553)
    ·
      refine ⟨24023916996041003656233415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32031889328054671541644553 24023916996041003656233415)
      ·
        refine ⟨36035875494061505484350123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24023916996041003656233415 36035875494061505484350123)
        ·
          refine ⟨54053813241092258226525185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36035875494061505484350123 54053813241092258226525185)
          ·
            refine ⟨40540359930819193669893889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54053813241092258226525185 40540359930819193669893889)
            ·
              refine ⟨30405269948114395252420417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40540359930819193669893889 30405269948114395252420417)
              ·
                refine ⟨22803952461085796439315313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30405269948114395252420417 22803952461085796439315313)
                ·
                  refine ⟨17102964345814347329486485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22803952461085796439315313 17102964345814347329486485)
                  ·
                    refine ⟨801701453710047531069679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17102964345814347329486485 801701453710047531069679)
                    ·
                      rfl

theorem cell22_2341962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2341962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341962 prefixEnd_2341962 := by exact prefixLift 2341962
  have htrace : WordTrace (prefixWord ++ tailWord_2341962) baseStart_2341962 baseEnd_2341962 := by
    simpa [prefixWord, tailWord_2341962, baseEnd_2341962] using wordTrace_append hprefix tailTrace_2341962
  have hstable : (prefixWord ++ tailWord_2341962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341962).length < 2 ^ (prefixWord ++ tailWord_2341962).sum := by decide
  have hdescent : baseEnd_2341962 < baseStart_2341962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341994 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_2341994 : Nat := 118140960795 + 2341994 * 2 ^ 59
def prefixEnd_2341994 : Nat := 4983230072969 + 3 ^ 40 * 2341994 * 2
def baseEnd_2341994 : Nat := 267237469321336704756527

theorem tailTrace_2341994 : CollatzResearch.WordTrace tailWord_2341994 prefixEnd_2341994 267237469321336704756527 := by
  unfold tailWord_2341994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21354884669340798394054259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56946359118242129050811357 21354884669340798394054259)
  ·
    refine ⟨32032327004011197591081389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21354884669340798394054259 32032327004011197591081389)
    ·
      refine ⟨12012122626504199096655521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32032327004011197591081389 12012122626504199096655521)
      ·
        refine ⟨9009091969878149322491641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12012122626504199096655521 9009091969878149322491641)
        ·
          refine ⟨6756818977408611991868731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9009091969878149322491641 6756818977408611991868731)
          ·
            refine ⟨10135228466112917987803097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6756818977408611991868731 10135228466112917987803097)
            ·
              refine ⟨7601421349584688490852323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10135228466112917987803097 7601421349584688490852323)
              ·
                refine ⟨11402132024377032736278485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7601421349584688490852323 11402132024377032736278485)
                ·
                  refine ⟨267237469321336704756527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11402132024377032736278485 267237469321336704756527)
                  ·
                    rfl

theorem cell22_2341994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_2341994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341994 prefixEnd_2341994 := by exact prefixLift 2341994
  have htrace : WordTrace (prefixWord ++ tailWord_2341994) baseStart_2341994 baseEnd_2341994 := by
    simpa [prefixWord, tailWord_2341994, baseEnd_2341994] using wordTrace_append hprefix tailTrace_2341994
  have hstable : (prefixWord ++ tailWord_2341994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341994).length < 2 ^ (prefixWord ++ tailWord_2341994).sum := by decide
  have hdescent : baseEnd_2341994 < baseStart_2341994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2341998 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2341998 : Nat := 118140960795 + 2341998 * 2 ^ 59
def prefixEnd_2341998 : Nat := 4983230072969 + 3 ^ 40 * 2341998 * 2
def baseEnd_2341998 : Nat := 801713777245755437169569

theorem tailTrace_2341998 : CollatzResearch.WordTrace tailWord_2341998 prefixEnd_2341998 801713777245755437169569 := by
  unfold tailWord_2341998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677460571168587782420331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56946456379565801506241765 10677460571168587782420331)
  ·
    refine ⟨16016190856752881673630497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10677460571168587782420331 16016190856752881673630497)
    ·
      refine ⟨12012143142564661255222873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16016190856752881673630497 12012143142564661255222873)
      ·
        refine ⟨9009107356923495941417155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12012143142564661255222873 9009107356923495941417155)
        ·
          refine ⟨13513661035385243912125733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9009107356923495941417155 13513661035385243912125733)
          ·
            refine ⟨2533811444134733233523575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13513661035385243912125733 2533811444134733233523575)
            ·
              refine ⟨3800717166202099850285363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2533811444134733233523575 3800717166202099850285363)
              ·
                refine ⟨5701075749303149775428045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3800717166202099850285363 5701075749303149775428045)
                ·
                  refine ⟨2137903405988681165785517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5701075749303149775428045 2137903405988681165785517)
                  ·
                    refine ⟨801713777245755437169569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137903405988681165785517 801713777245755437169569)
                    ·
                      rfl

theorem cell22_2341998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2341998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2341998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2341998 prefixEnd_2341998 := by exact prefixLift 2341998
  have htrace : WordTrace (prefixWord ++ tailWord_2341998) baseStart_2341998 baseEnd_2341998 := by
    simpa [prefixWord, tailWord_2341998, baseEnd_2341998] using wordTrace_append hprefix tailTrace_2341998
  have hstable : (prefixWord ++ tailWord_2341998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2341998).length < 2 ^ (prefixWord ++ tailWord_2341998).sum := by decide
  have hdescent : baseEnd_2341998 < baseStart_2341998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2341998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342071 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 2, 3]
def baseStart_2342071 : Nat := 118140960795 + 2342071 * 2 ^ 59
def prefixEnd_2342071 : Nat := 4983230072969 + 3 ^ 40 * 2342071 * 2
def baseEnd_2342071 : Nat := 801738766637607580094345

theorem tailTrace_2342071 : CollatzResearch.WordTrace tailWord_2342071 prefixEnd_2342071 801738766637607580094345 := by
  unfold tailWord_2342071
  simp only [CollatzResearch.WordTrace]
  refine ⟨85422347098084235726770067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56948231398722823817846711 85422347098084235726770067)
  ·
    refine ⟨128133520647126353590155101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85422347098084235726770067 128133520647126353590155101)
    ·
      refine ⟨48050070242672382596308163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128133520647126353590155101 48050070242672382596308163)
      ·
        refine ⟨72075105364008573894462245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48050070242672382596308163 72075105364008573894462245)
        ·
          refine ⟨13514082255751607605211671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72075105364008573894462245 13514082255751607605211671)
          ·
            refine ⟨20271123383627411407817507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13514082255751607605211671 20271123383627411407817507)
            ·
              refine ⟨30406685075441117111726261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20271123383627411407817507 30406685075441117111726261)
              ·
                refine ⟨2850626725822604729224337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30406685075441117111726261 2850626725822604729224337)
                ·
                  refine ⟨2137970044366953546918253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850626725822604729224337 2137970044366953546918253)
                  ·
                    refine ⟨801738766637607580094345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2137970044366953546918253 801738766637607580094345)
                    ·
                      rfl

theorem cell22_2342071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_2342071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342071 prefixEnd_2342071 := by exact prefixLift 2342071
  have htrace : WordTrace (prefixWord ++ tailWord_2342071) baseStart_2342071 baseEnd_2342071 := by
    simpa [prefixWord, tailWord_2342071, baseEnd_2342071] using wordTrace_append hprefix tailTrace_2342071
  have hstable : (prefixWord ++ tailWord_2342071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342071).length < 2 ^ (prefixWord ++ tailWord_2342071).sum := by decide
  have hdescent : baseEnd_2342071 < baseStart_2342071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342116 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_2342116 : Nat := 118140960795 + 2342116 * 2 ^ 59
def prefixEnd_2342116 : Nat := 4983230072969 + 3 ^ 40 * 2342116 * 2
def baseEnd_2342116 : Nat := 801754171057242462719207

theorem tailTrace_2342116 : CollatzResearch.WordTrace tailWord_2342116 prefixEnd_2342116 801754171057242462719207 := by
  unfold tailWord_2342116
  simp only [CollatzResearch.WordTrace]
  refine ⟨42711994191460604206079101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56949325588614138941438801 42711994191460604206079101)
  ·
    refine ⟨16016997821797726577279663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42711994191460604206079101 16016997821797726577279663)
    ·
      refine ⟨24025496732696589865919495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16016997821797726577279663 24025496732696589865919495)
      ·
        refine ⟨36038245099044884798879243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24025496732696589865919495 36038245099044884798879243)
        ·
          refine ⟨54057367648567327198318865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36038245099044884798879243 54057367648567327198318865)
          ·
            refine ⟨40543025736425495398739149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54057367648567327198318865 40543025736425495398739149)
            ·
              refine ⟨15203634651159560774527181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40543025736425495398739149 15203634651159560774527181)
              ·
                refine ⟨5701362994184835290447693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15203634651159560774527181 5701362994184835290447693)
                ·
                  refine ⟨2138011122819313233917885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5701362994184835290447693 2138011122819313233917885)
                  ·
                    refine ⟨801754171057242462719207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138011122819313233917885 801754171057242462719207)
                    ·
                      rfl

theorem cell22_2342116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_2342116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342116 prefixEnd_2342116 := by exact prefixLift 2342116
  have htrace : WordTrace (prefixWord ++ tailWord_2342116) baseStart_2342116 baseEnd_2342116 := by
    simpa [prefixWord, tailWord_2342116, baseEnd_2342116] using wordTrace_append hprefix tailTrace_2342116
  have hstable : (prefixWord ++ tailWord_2342116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342116).length < 2 ^ (prefixWord ++ tailWord_2342116).sum := by decide
  have hdescent : baseEnd_2342116 < baseStart_2342116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342159 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2342159 : Nat := 118140960795 + 2342159 * 2 ^ 59
def prefixEnd_2342159 : Nat := 4983230072969 + 3 ^ 40 * 2342159 * 2
def baseEnd_2342159 : Nat := 801768890836004683894075

theorem tailTrace_2342159 : CollatzResearch.WordTrace tailWord_2342159 prefixEnd_2342159 801768890836004683894075 := by
  unfold tailWord_2342159
  simp only [CollatzResearch.WordTrace]
  refine ⟨85425556721765426755973531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56950371147843617837315687 85425556721765426755973531)
  ·
    refine ⟨128138335082648140133960297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85425556721765426755973531 128138335082648140133960297)
    ·
      refine ⟨96103751311986105100470223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128138335082648140133960297 96103751311986105100470223)
      ·
        refine ⟨144155626967979157650705335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96103751311986105100470223 144155626967979157650705335)
        ·
          refine ⟨216233440451968736476058003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144155626967979157650705335 216233440451968736476058003)
          ·
            refine ⟨324350160677953104714087005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216233440451968736476058003 324350160677953104714087005)
            ·
              refine ⟨121631310254232414267782627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 324350160677953104714087005 121631310254232414267782627)
              ·
                refine ⟨182446965381348621401673941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121631310254232414267782627 182446965381348621401673941)
                ·
                  refine ⟨4276100751125358314101733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 182446965381348621401673941 4276100751125358314101733)
                  ·
                    refine ⟨801768890836004683894075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276100751125358314101733 801768890836004683894075)
                    ·
                      rfl

theorem cell22_2342159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2342159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342159 prefixEnd_2342159 := by exact prefixLift 2342159
  have htrace : WordTrace (prefixWord ++ tailWord_2342159) baseStart_2342159 baseEnd_2342159 := by
    simpa [prefixWord, tailWord_2342159, baseEnd_2342159] using wordTrace_append hprefix tailTrace_2342159
  have hstable : (prefixWord ++ tailWord_2342159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342159).length < 2 ^ (prefixWord ++ tailWord_2342159).sum := by decide
  have hdescent : baseEnd_2342159 < baseStart_2342159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342193 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2342193 : Nat := 118140960795 + 2342193 * 2 ^ 59
def prefixEnd_2342193 : Nat := 4983230072969 + 3 ^ 40 * 2342193 * 2
def baseEnd_2342193 : Nat := 801780529730839928543971

theorem tailTrace_2342193 : CollatzResearch.WordTrace tailWord_2342193 prefixEnd_2342193 801780529730839928543971 := by
  unfold tailWord_2342193
  simp only [CollatzResearch.WordTrace]
  refine ⟨85426796803642250562711233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56951197869094833708474155 85426796803642250562711233)
  ·
    refine ⟨64070097602731687922033425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85426796803642250562711233 64070097602731687922033425)
    ·
      refine ⟨48052573202048765941525069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64070097602731687922033425 48052573202048765941525069)
      ·
        refine ⟨18019714950768287228071901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48052573202048765941525069 18019714950768287228071901)
        ·
          refine ⟨6757393106538107710526963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18019714950768287228071901 6757393106538107710526963)
          ·
            refine ⟨10136089659807161565790445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6757393106538107710526963 10136089659807161565790445)
            ·
              refine ⟨3801033622427685587171417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10136089659807161565790445 3801033622427685587171417)
              ·
                refine ⟨2850775216820764190378563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801033622427685587171417 2850775216820764190378563)
                ·
                  refine ⟨4276162825231146285567845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850775216820764190378563 4276162825231146285567845)
                  ·
                    refine ⟨801780529730839928543971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276162825231146285567845 801780529730839928543971)
                    ·
                      rfl

theorem cell22_2342193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2342193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342193 prefixEnd_2342193 := by exact prefixLift 2342193
  have htrace : WordTrace (prefixWord ++ tailWord_2342193) baseStart_2342193 baseEnd_2342193 := by
    simpa [prefixWord, tailWord_2342193, baseEnd_2342193] using wordTrace_append hprefix tailTrace_2342193
  have hstable : (prefixWord ++ tailWord_2342193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342193).length < 2 ^ (prefixWord ++ tailWord_2342193).sum := by decide
  have hdescent : baseEnd_2342193 < baseStart_2342193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342253 : List Nat := [1, 5, 1, 1, 1, 4, 3, 6]
def baseStart_2342253 : Nat := 118140960795 + 2342253 * 2 ^ 59
def prefixEnd_2342253 : Nat := 4983230072969 + 3 ^ 40 * 2342253 * 2
def baseEnd_2342253 : Nat := 89089007661891085782643

theorem tailTrace_2342253 : CollatzResearch.WordTrace tailWord_2342253 prefixEnd_2342253 89089007661891085782643 := by
  unfold tailWord_2342253
  simp only [CollatzResearch.WordTrace]
  refine ⟨85428985183424880809895413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56952656788949920539930275 85428985183424880809895413)
  ·
    refine ⟨8008967360946082575927695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85428985183424880809895413 8008967360946082575927695)
    ·
      refine ⟨12013451041419123863891543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8008967360946082575927695 12013451041419123863891543)
      ·
        refine ⟨18020176562128685795837315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12013451041419123863891543 18020176562128685795837315)
        ·
          refine ⟨27030264843193028693755973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18020176562128685795837315 27030264843193028693755973)
          ·
            refine ⟨5068174658098692880079245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27030264843193028693755973 5068174658098692880079245)
            ·
              refine ⟨1900565496787009830029717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5068174658098692880079245 1900565496787009830029717)
              ·
                refine ⟨89089007661891085782643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1900565496787009830029717 89089007661891085782643)
                ·
                  rfl

theorem cell22_2342253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 6].length) (baseStart_2342253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342253 prefixEnd_2342253 := by exact prefixLift 2342253
  have htrace : WordTrace (prefixWord ++ tailWord_2342253) baseStart_2342253 baseEnd_2342253 := by
    simpa [prefixWord, tailWord_2342253, baseEnd_2342253] using wordTrace_append hprefix tailTrace_2342253
  have hstable : (prefixWord ++ tailWord_2342253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342253).length < 2 ^ (prefixWord ++ tailWord_2342253).sum := by decide
  have hdescent : baseEnd_2342253 < baseStart_2342253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342270 : List Nat := [4, 2, 3, 2, 1, 1, 9]
def baseStart_2342270 : Nat := 118140960795 + 2342270 * 2 ^ 59
def prefixEnd_2342270 : Nat := 4983230072969 + 3 ^ 40 * 2342270 * 2
def baseEnd_2342270 : Nat := 29696551422386570161805

theorem tailTrace_2342270 : CollatzResearch.WordTrace tailWord_2342270 prefixEnd_2342270 29696551422386570161805 := by
  unfold tailWord_2342270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678700653045411589158033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56953070149575528475509509 10678700653045411589158033)
  ·
    refine ⟨8009025489784058691868525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10678700653045411589158033 8009025489784058691868525)
    ·
      refine ⟨3003384558669022009450697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8009025489784058691868525 3003384558669022009450697)
      ·
        refine ⟨2252538419001766507088023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3003384558669022009450697 2252538419001766507088023)
        ·
          refine ⟨3378807628502649760632035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2252538419001766507088023 3378807628502649760632035)
          ·
            refine ⟨5068211442753974640948053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378807628502649760632035 5068211442753974640948053)
            ·
              refine ⟨29696551422386570161805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5068211442753974640948053 29696551422386570161805)
              ·
                rfl

theorem cell22_2342270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 9].length) (baseStart_2342270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342270 prefixEnd_2342270 := by exact prefixLift 2342270
  have htrace : WordTrace (prefixWord ++ tailWord_2342270) baseStart_2342270 baseEnd_2342270 := by
    simpa [prefixWord, tailWord_2342270, baseEnd_2342270] using wordTrace_append hprefix tailTrace_2342270
  have hstable : (prefixWord ++ tailWord_2342270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342270).length < 2 ^ (prefixWord ++ tailWord_2342270).sum := by decide
  have hdescent : baseEnd_2342270 < baseStart_2342270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342274 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2342274 : Nat := 118140960795 + 2342274 * 2 ^ 59
def prefixEnd_2342274 : Nat := 4983230072969 + 3 ^ 40 * 2342274 * 2
def baseEnd_2342274 : Nat := 801808257686182717268723

theorem tailTrace_2342274 : CollatzResearch.WordTrace tailWord_2342274 prefixEnd_2342274 801808257686182717268723 := by
  unfold tailWord_2342274
  simp only [CollatzResearch.WordTrace]
  refine ⟨21357437779087200349102469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56953167410899200930939917 21357437779087200349102469)
  ·
    refine ⟨4004519583578850065456713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21357437779087200349102469 4004519583578850065456713)
    ·
      refine ⟨3003389687684137549092535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4004519583578850065456713 3003389687684137549092535)
      ·
        refine ⟨4505084531526206323638803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003389687684137549092535 4505084531526206323638803)
        ·
          refine ⟨6757626797289309485458205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4505084531526206323638803 6757626797289309485458205)
          ·
            refine ⟨2534110048983491057046827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6757626797289309485458205 2534110048983491057046827)
            ·
              refine ⟨3801165073475236585570241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534110048983491057046827 3801165073475236585570241)
              ·
                refine ⟨2850873805106427439177681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801165073475236585570241 2850873805106427439177681)
                ·
                  refine ⟨2138155353829820579383261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2850873805106427439177681 2138155353829820579383261)
                  ·
                    refine ⟨801808257686182717268723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138155353829820579383261 801808257686182717268723)
                    ·
                      rfl

theorem cell22_2342274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2342274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342274 prefixEnd_2342274 := by exact prefixLift 2342274
  have htrace : WordTrace (prefixWord ++ tailWord_2342274) baseStart_2342274 baseEnd_2342274 := by
    simpa [prefixWord, tailWord_2342274, baseEnd_2342274] using wordTrace_append hprefix tailTrace_2342274
  have hstable : (prefixWord ++ tailWord_2342274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342274).length < 2 ^ (prefixWord ++ tailWord_2342274).sum := by decide
  have hdescent : baseEnd_2342274 < baseStart_2342274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342328 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_2342328 : Nat := 118140960795 + 2342328 * 2 ^ 59
def prefixEnd_2342328 : Nat := 4983230072969 + 3 ^ 40 * 2342328 * 2
def baseEnd_2342328 : Nat := 801826742989744576418557

theorem tailTrace_2342328 : CollatzResearch.WordTrace tailWord_2342328 prefixEnd_2342328 801826742989744576418557 := by
  unfold tailWord_2342328
  simp only [CollatzResearch.WordTrace]
  refine ⟨42715860329076584309437819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56954480438768779079250425 42715860329076584309437819)
  ·
    refine ⟨64073790493614876464156729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42715860329076584309437819 64073790493614876464156729)
    ·
      refine ⟨48055342870211157348117547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64073790493614876464156729 48055342870211157348117547)
      ·
        refine ⟨72083014305316736022176321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48055342870211157348117547 72083014305316736022176321)
        ·
          refine ⟨54062260728987552016632241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72083014305316736022176321 54062260728987552016632241)
          ·
            refine ⟨40546695546740664012474181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54062260728987552016632241 40546695546740664012474181)
            ·
              refine ⟨7602505415013874502338909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40546695546740664012474181 7602505415013874502338909)
              ·
                refine ⟨2850939530630202938377091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7602505415013874502338909 2850939530630202938377091)
                ·
                  refine ⟨4276409295945304407565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2850939530630202938377091 4276409295945304407565637)
                  ·
                    refine ⟨801826742989744576418557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276409295945304407565637 801826742989744576418557)
                    ·
                      rfl

theorem cell22_2342328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_2342328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342328 prefixEnd_2342328 := by exact prefixLift 2342328
  have htrace : WordTrace (prefixWord ++ tailWord_2342328) baseStart_2342328 baseEnd_2342328 := by
    simpa [prefixWord, tailWord_2342328, baseEnd_2342328] using wordTrace_append hprefix tailTrace_2342328
  have hstable : (prefixWord ++ tailWord_2342328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342328).length < 2 ^ (prefixWord ++ tailWord_2342328).sum := by decide
  have hdescent : baseEnd_2342328 < baseStart_2342328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342390 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_2342390 : Nat := 118140960795 + 2342390 * 2 ^ 59
def prefixEnd_2342390 : Nat := 4983230072969 + 3 ^ 40 * 2342390 * 2
def baseEnd_2342390 : Nat := 801847966856797081368367

theorem tailTrace_2342390 : CollatzResearch.WordTrace tailWord_2342390 prefixEnd_2342390 801847966856797081368367 := by
  unfold tailWord_2342390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339623873995534575477039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56955987989285702138421749 5339623873995534575477039)
  ·
    refine ⟨8009435810993301863215559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5339623873995534575477039 8009435810993301863215559)
    ·
      refine ⟨12014153716489952794823339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8009435810993301863215559 12014153716489952794823339)
      ·
        refine ⟨18021230574734929192235009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12014153716489952794823339 18021230574734929192235009)
        ·
          refine ⟨13515922931051196894176257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18021230574734929192235009 13515922931051196894176257)
          ·
            refine ⟨10136942198288397670632193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13515922931051196894176257 10136942198288397670632193)
            ·
              refine ⟨7602706648716298252974145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10136942198288397670632193 7602706648716298252974145)
              ·
                refine ⟨5702029986537223689730609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7602706648716298252974145 5702029986537223689730609)
                ·
                  refine ⟨4276522489902917767297957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5702029986537223689730609 4276522489902917767297957)
                  ·
                    refine ⟨801847966856797081368367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276522489902917767297957 801847966856797081368367)
                    ·
                      rfl

theorem cell22_2342390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_2342390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342390 prefixEnd_2342390 := by exact prefixLift 2342390
  have htrace : WordTrace (prefixWord ++ tailWord_2342390) baseStart_2342390 baseEnd_2342390 := by
    simpa [prefixWord, tailWord_2342390, baseEnd_2342390] using wordTrace_append hprefix tailTrace_2342390
  have hstable : (prefixWord ++ tailWord_2342390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342390).length < 2 ^ (prefixWord ++ tailWord_2342390).sum := by decide
  have hdescent : baseEnd_2342390 < baseStart_2342390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342430 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2342430 : Nat := 118140960795 + 2342430 * 2 ^ 59
def prefixEnd_2342430 : Nat := 4983230072969 + 3 ^ 40 * 2342430 * 2
def baseEnd_2342430 : Nat := 801861659674250310368245

theorem tailTrace_2342430 : CollatzResearch.WordTrace tailWord_2342430 prefixEnd_2342430 801861659674250310368245 := by
  unfold tailWord_2342430
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679430112972955004886093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56956960602522426692725829 10679430112972955004886093)
  ·
    refine ⟨4004786292364858126832285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10679430112972955004886093 4004786292364858126832285)
    ·
      refine ⟨1501794859636821797562107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4004786292364858126832285 1501794859636821797562107)
      ·
        refine ⟨2252692289455232696343161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501794859636821797562107 2252692289455232696343161)
        ·
          refine ⟨1689519217091424522257371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2252692289455232696343161 1689519217091424522257371)
          ·
            refine ⟨2534278825637136783386057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1689519217091424522257371 2534278825637136783386057)
            ·
              refine ⟨1900709119227852587539543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534278825637136783386057 1900709119227852587539543)
              ·
                refine ⟨2851063678841778881309315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900709119227852587539543 2851063678841778881309315)
                ·
                  refine ⟨4276595518262668321963973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851063678841778881309315 4276595518262668321963973)
                  ·
                    refine ⟨801861659674250310368245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276595518262668321963973 801861659674250310368245)
                    ·
                      rfl

theorem cell22_2342430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2342430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342430 prefixEnd_2342430 := by exact prefixLift 2342430
  have htrace : WordTrace (prefixWord ++ tailWord_2342430) baseStart_2342430 baseEnd_2342430 := by
    simpa [prefixWord, tailWord_2342430, baseEnd_2342430] using wordTrace_append hprefix tailTrace_2342430
  have hstable : (prefixWord ++ tailWord_2342430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342430).length < 2 ^ (prefixWord ++ tailWord_2342430).sum := by decide
  have hdescent : baseEnd_2342430 < baseStart_2342430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342454 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2342454 : Nat := 118140960795 + 2342454 * 2 ^ 59
def prefixEnd_2342454 : Nat := 4983230072969 + 3 ^ 40 * 2342454 * 2
def baseEnd_2342454 : Nat := 801869875364722247768171

theorem tailTrace_2342454 : CollatzResearch.WordTrace tailWord_2342454 prefixEnd_2342454 801869875364722247768171 := by
  unfold tailWord_2342454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5339769765981043258622651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56957544170464461425308277 5339769765981043258622651)
  ·
    refine ⟨8009654648971564887933977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5339769765981043258622651 8009654648971564887933977)
    ·
      refine ⟨6007240986728673665950483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8009654648971564887933977 6007240986728673665950483)
      ·
        refine ⟨9010861480093010498925725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007240986728673665950483 9010861480093010498925725)
        ·
          refine ⟨3379073055034878937097147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9010861480093010498925725 3379073055034878937097147)
          ·
            refine ⟨5068609582552318405645721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379073055034878937097147 5068609582552318405645721)
            ·
              refine ⟨3801457186914238804234291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068609582552318405645721 3801457186914238804234291)
              ·
                refine ⟨5702185780371358206351437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801457186914238804234291 5702185780371358206351437)
                ·
                  refine ⟨2138319667639259327381789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5702185780371358206351437 2138319667639259327381789)
                  ·
                    refine ⟨801869875364722247768171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138319667639259327381789 801869875364722247768171)
                    ·
                      rfl

theorem cell22_2342454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2342454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342454 prefixEnd_2342454 := by exact prefixLift 2342454
  have htrace : WordTrace (prefixWord ++ tailWord_2342454) baseStart_2342454 baseEnd_2342454 := by
    simpa [prefixWord, tailWord_2342454, baseEnd_2342454] using wordTrace_append hprefix tailTrace_2342454
  have hstable : (prefixWord ++ tailWord_2342454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342454).length < 2 ^ (prefixWord ++ tailWord_2342454).sum := by decide
  have hdescent : baseEnd_2342454 < baseStart_2342454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342480 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_2342480 : Nat := 118140960795 + 2342480 * 2 ^ 59
def prefixEnd_2342480 : Nat := 4983230072969 + 3 ^ 40 * 2342480 * 2
def baseEnd_2342480 : Nat := 801878775696066846618091

theorem tailTrace_2342480 : CollatzResearch.WordTrace tailWord_2342480 prefixEnd_2342480 801878775696066846618091 := by
  unfold tailWord_2342480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42718632276801249289204447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56958176369068332385605929 42718632276801249289204447)
  ·
    refine ⟨64077948415201873933806671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42718632276801249289204447 64077948415201873933806671)
    ·
      refine ⟨96116922622802810900710007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64077948415201873933806671 96116922622802810900710007)
      ·
        refine ⟨144175383934204216351065011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96116922622802810900710007 144175383934204216351065011)
        ·
          refine ⟨216263075901306324526597517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144175383934204216351065011 216263075901306324526597517)
          ·
            refine ⟨81098653462989871697474069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 216263075901306324526597517 81098653462989871697474069)
            ·
              refine ⟨3801499381077650235819097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81098653462989871697474069 3801499381077650235819097)
              ·
                refine ⟨2851124535808237676864323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3801499381077650235819097 2851124535808237676864323)
                ·
                  refine ⟨4276686803712356515296485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2851124535808237676864323 4276686803712356515296485)
                  ·
                    refine ⟨801878775696066846618091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276686803712356515296485 801878775696066846618091)
                    ·
                      rfl

theorem cell22_2342480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_2342480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342480 prefixEnd_2342480 := by exact prefixLift 2342480
  have htrace : WordTrace (prefixWord ++ tailWord_2342480) baseStart_2342480 baseEnd_2342480 := by
    simpa [prefixWord, tailWord_2342480, baseEnd_2342480] using wordTrace_append hprefix tailTrace_2342480
  have hstable : (prefixWord ++ tailWord_2342480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342480).length < 2 ^ (prefixWord ++ tailWord_2342480).sum := by decide
  have hdescent : baseEnd_2342480 < baseStart_2342480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342523 : List Nat := [1, 1, 1, 1, 1, 4, 6, 7]
def baseStart_2342523 : Nat := 118140960795 + 2342523 * 2 ^ 59
def prefixEnd_2342523 : Nat := 4983230072969 + 3 ^ 40 * 2342523 * 2
def baseEnd_2342523 : Nat := 89099277274981007532551

theorem tailTrace_2342523 : CollatzResearch.WordTrace tailWord_2342523 prefixEnd_2342523 89099277274981007532551 := by
  unfold tailWord_2342523
  simp only [CollatzResearch.WordTrace]
  refine ⟨85438832892446716922224223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56959221928297811281482815 85438832892446716922224223)
  ·
    refine ⟨128158249338670075383336335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85438832892446716922224223 128158249338670075383336335)
    ·
      refine ⟨192237374008005113075004503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128158249338670075383336335 192237374008005113075004503)
      ·
        refine ⟨288356061012007669612506755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192237374008005113075004503 288356061012007669612506755)
        ·
          refine ⟨432534091518011504418760133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288356061012007669612506755 432534091518011504418760133)
          ·
            refine ⟨81100142159627157078517525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 432534091518011504418760133 81100142159627157078517525)
            ·
              refine ⟨3801569163732522988055509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81100142159627157078517525 3801569163732522988055509)
              ·
                refine ⟨89099277274981007532551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3801569163732522988055509 89099277274981007532551)
                ·
                  rfl

theorem cell22_2342523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 7].length) (baseStart_2342523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342523 prefixEnd_2342523 := by exact prefixLift 2342523
  have htrace : WordTrace (prefixWord ++ tailWord_2342523) baseStart_2342523 baseEnd_2342523 := by
    simpa [prefixWord, tailWord_2342523, baseEnd_2342523] using wordTrace_append hprefix tailTrace_2342523
  have hstable : (prefixWord ++ tailWord_2342523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342523).length < 2 ^ (prefixWord ++ tailWord_2342523).sum := by decide
  have hdescent : baseEnd_2342523 < baseStart_2342523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342542 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_2342542 : Nat := 118140960795 + 2342542 * 2 ^ 59
def prefixEnd_2342542 : Nat := 4983230072969 + 3 ^ 40 * 2342542 * 2
def baseEnd_2342542 : Nat := 801899999563119351567901

theorem tailTrace_2342542 : CollatzResearch.WordTrace tailWord_2342542 prefixEnd_2342542 801899999563119351567901 := by
  unfold tailWord_2342542
  simp only [CollatzResearch.WordTrace]
  refine ⟨10679940734922235395895735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56959683919585255444777253 10679940734922235395895735)
  ·
    refine ⟨16019911102383353093843603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10679940734922235395895735 16019911102383353093843603)
    ·
      refine ⟨24029866653575029640765405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16019911102383353093843603 24029866653575029640765405)
      ·
        refine ⟨9011199995090636115287027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24029866653575029640765405 9011199995090636115287027)
        ·
          refine ⟨13516799992635954172930541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011199995090636115287027 13516799992635954172930541)
          ·
            refine ⟨5068799997238482814848953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13516799992635954172930541 5068799997238482814848953)
            ·
              refine ⟨3801599997928862111136715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068799997238482814848953 3801599997928862111136715)
              ·
                refine ⟨5702399996893293166705073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3801599997928862111136715 5702399996893293166705073)
                ·
                  refine ⟨4276799997669969875028805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5702399996893293166705073 4276799997669969875028805)
                  ·
                    refine ⟨801899999563119351567901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4276799997669969875028805 801899999563119351567901)
                    ·
                      rfl

theorem cell22_2342542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_2342542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342542 prefixEnd_2342542 := by exact prefixLift 2342542
  have htrace : WordTrace (prefixWord ++ tailWord_2342542) baseStart_2342542 baseEnd_2342542 := by
    simpa [prefixWord, tailWord_2342542, baseEnd_2342542] using wordTrace_append hprefix tailTrace_2342542
  have hstable : (prefixWord ++ tailWord_2342542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342542).length < 2 ^ (prefixWord ++ tailWord_2342542).sum := by decide
  have hdescent : baseEnd_2342542 < baseStart_2342542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342574 : List Nat := [4, 1, 4, 1, 2, 2, 1, 7]
def baseStart_2342574 : Nat := 118140960795 + 2342574 * 2 ^ 59
def prefixEnd_2342574 : Nat := 4983230072969 + 3 ^ 40 * 2342574 * 2
def baseEnd_2342574 : Nat := 89101217090786881640867

theorem tailTrace_2342574 : CollatzResearch.WordTrace tailWord_2342574 prefixEnd_2342574 89101217090786881640867 := by
  unfold tailWord_2342574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10680086626907744079041347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56960462010174635088220517 10680086626907744079041347)
  ·
    refine ⟨16020129940361616118562021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10680086626907744079041347 16020129940361616118562021)
    ·
      refine ⟨3003774363817803022230379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16020129940361616118562021 3003774363817803022230379)
      ·
        refine ⟨4505661545726704533345569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003774363817803022230379 4505661545726704533345569)
        ·
          refine ⟨3379246159295028400009177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4505661545726704533345569 3379246159295028400009177)
          ·
            refine ⟨2534434619471271300006883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379246159295028400009177 2534434619471271300006883)
            ·
              refine ⟨3801651929206906950010325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2534434619471271300006883 3801651929206906950010325)
              ·
                refine ⟨89101217090786881640867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3801651929206906950010325 89101217090786881640867)
                ·
                  rfl

theorem cell22_2342574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_2342574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342574 prefixEnd_2342574 := by exact prefixLift 2342574
  have htrace : WordTrace (prefixWord ++ tailWord_2342574) baseStart_2342574 baseEnd_2342574 := by
    simpa [prefixWord, tailWord_2342574, baseEnd_2342574] using wordTrace_append hprefix tailTrace_2342574
  have hstable : (prefixWord ++ tailWord_2342574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342574).length < 2 ^ (prefixWord ++ tailWord_2342574).sum := by decide
  have hdescent : baseEnd_2342574 < baseStart_2342574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342585 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 5]
def baseStart_2342585 : Nat := 118140960795 + 2342585 * 2 ^ 59
def prefixEnd_2342585 : Nat := 4983230072969 + 3 ^ 40 * 2342585 * 2
def baseEnd_2342585 : Nat := 267304906447293857580923

theorem tailTrace_2342585 : CollatzResearch.WordTrace tailWord_2342585 prefixEnd_2342585 267304906447293857580923 := by
  unfold tailWord_2342585
  simp only [CollatzResearch.WordTrace]
  refine ⟨85441094218222101510981209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56960729478814734340654139 85441094218222101510981209)
  ·
    refine ⟨64080820663666576133235907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85441094218222101510981209 64080820663666576133235907)
    ·
      refine ⟨96121230995499864199853861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64080820663666576133235907 96121230995499864199853861)
      ·
        refine ⟨18022730811656224537472599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96121230995499864199853861 18022730811656224537472599)
        ·
          refine ⟨27034096217484336806208899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18022730811656224537472599 27034096217484336806208899)
          ·
            refine ⟨40551144326226505209313349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27034096217484336806208899 40551144326226505209313349)
            ·
              refine ⟨7603339561167469726746253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40551144326226505209313349 7603339561167469726746253)
              ·
                refine ⟨2851252335437801147529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7603339561167469726746253 2851252335437801147529845)
                ·
                  refine ⟨267304906447293857580923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2851252335437801147529845 267304906447293857580923)
                  ·
                    rfl

theorem cell22_2342585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_2342585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342585 prefixEnd_2342585 := by exact prefixLift 2342585
  have htrace : WordTrace (prefixWord ++ tailWord_2342585) baseStart_2342585 baseEnd_2342585 := by
    simpa [prefixWord, tailWord_2342585, baseEnd_2342585] using wordTrace_append hprefix tailTrace_2342585
  have hstable : (prefixWord ++ tailWord_2342585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342585).length < 2 ^ (prefixWord ++ tailWord_2342585).sum := by decide
  have hdescent : baseEnd_2342585 < baseStart_2342585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342677 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2342677 : Nat := 118140960795 + 2342677 * 2 ^ 59
def prefixEnd_2342677 : Nat := 4983230072969 + 3 ^ 40 * 2342677 * 2
def baseEnd_2342677 : Nat := 801946212822023999442487

theorem tailTrace_2342677 : CollatzResearch.WordTrace tailWord_2342677 prefixEnd_2342677 801946212822023999442487 := by
  unfold tailWord_2342677
  simp only [CollatzResearch.WordTrace]
  refine ⟨85444449733888801223330285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56962966489259200815553523 85444449733888801223330285)
  ·
    refine ⟨32041668650208300458748857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85444449733888801223330285 32041668650208300458748857)
    ·
      refine ⟨24031251487656225344061643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32041668650208300458748857 24031251487656225344061643)
      ·
        refine ⟨36046877231484338016092465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24031251487656225344061643 36046877231484338016092465)
        ·
          refine ⟨27035157923613253512069349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36046877231484338016092465 27035157923613253512069349)
          ·
            refine ⟨5069092110677485033513003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27035157923613253512069349 5069092110677485033513003)
            ·
              refine ⟨7603638166016227550269505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069092110677485033513003 7603638166016227550269505)
              ·
                refine ⟨5702728624512170662702129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7603638166016227550269505 5702728624512170662702129)
                ·
                  refine ⟨4277046468384127997026597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5702728624512170662702129 4277046468384127997026597)
                  ·
                    refine ⟨801946212822023999442487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4277046468384127997026597 801946212822023999442487)
                    ·
                      rfl

theorem cell22_2342677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2342677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342677 prefixEnd_2342677 := by exact prefixLift 2342677
  have htrace : WordTrace (prefixWord ++ tailWord_2342677) baseStart_2342677 baseEnd_2342677 := by
    simpa [prefixWord, tailWord_2342677, baseEnd_2342677] using wordTrace_append hprefix tailTrace_2342677
  have hstable : (prefixWord ++ tailWord_2342677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342677).length < 2 ^ (prefixWord ++ tailWord_2342677).sum := by decide
  have hdescent : baseEnd_2342677 < baseStart_2342677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342692 : List Nat := [2, 3, 1, 3, 2, 2, 2, 7]
def baseStart_2342692 : Nat := 118140960795 + 2342692 * 2 ^ 59
def prefixEnd_2342692 : Nat := 4983230072969 + 3 ^ 40 * 2342692 * 2
def baseEnd_2342692 : Nat := 89105705292063217813049

theorem tailTrace_2342692 : CollatzResearch.WordTrace tailWord_2342692 prefixEnd_2342692 89105705292063217813049 := by
  unfold tailWord_2342692
  simp only [CollatzResearch.WordTrace]
  refine ⟨42722498414417229392563165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56963331219222972523417553 42722498414417229392563165)
  ·
    refine ⟨16020936905406461022211187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42722498414417229392563165 16020936905406461022211187)
    ·
      refine ⟨24031405358109691533316781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16020936905406461022211187 24031405358109691533316781)
      ·
        refine ⟨9011777009291134324993793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24031405358109691533316781 9011777009291134324993793)
        ·
          refine ⟨6758832756968350743745345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9011777009291134324993793 6758832756968350743745345)
          ·
            refine ⟨5069124567726263057809009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6758832756968350743745345 5069124567726263057809009)
            ·
              refine ⟨3801843425794697293356757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5069124567726263057809009 3801843425794697293356757)
              ·
                refine ⟨89105705292063217813049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3801843425794697293356757 89105705292063217813049)
                ·
                  rfl

theorem cell22_2342692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_2342692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342692 prefixEnd_2342692 := by exact prefixLift 2342692
  have htrace : WordTrace (prefixWord ++ tailWord_2342692) baseStart_2342692 baseEnd_2342692 := by
    simpa [prefixWord, tailWord_2342692, baseEnd_2342692] using wordTrace_append hprefix tailTrace_2342692
  have hstable : (prefixWord ++ tailWord_2342692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342692).length < 2 ^ (prefixWord ++ tailWord_2342692).sum := by decide
  have hdescent : baseEnd_2342692 < baseStart_2342692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342696 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2342696 : Nat := 118140960795 + 2342696 * 2 ^ 59
def prefixEnd_2342696 : Nat := 4983230072969 + 3 ^ 40 * 2342696 * 2
def baseEnd_2342696 : Nat := 801952716910314283217429

theorem tailTrace_2342696 : CollatzResearch.WordTrace tailWord_2342696 prefixEnd_2342696 801952716910314283217429 := by
  unfold tailWord_2342696
  simp only [CollatzResearch.WordTrace]
  refine ⟨42722571360409983734135971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56963428480546644978847961 42722571360409983734135971)
  ·
    refine ⟨64083857040614975601203957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42722571360409983734135971 64083857040614975601203957)
    ·
      refine ⟨6007861597557653962612871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64083857040614975601203957 6007861597557653962612871)
      ·
        refine ⟨9011792396336480943919307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6007861597557653962612871 9011792396336480943919307)
        ·
          refine ⟨13517688594504721415878961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9011792396336480943919307 13517688594504721415878961)
          ·
            refine ⟨10138266445878541061909221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13517688594504721415878961 10138266445878541061909221)
            ·
              refine ⟨1900924958602226449107979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10138266445878541061909221 1900924958602226449107979)
              ·
                refine ⟨2851387437903339673661969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1900924958602226449107979 2851387437903339673661969)
                ·
                  refine ⟨2138540578427504755246477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851387437903339673661969 2138540578427504755246477)
                  ·
                    refine ⟨801952716910314283217429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138540578427504755246477 801952716910314283217429)
                    ·
                      rfl

theorem cell22_2342696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2342696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342696 prefixEnd_2342696 := by exact prefixLift 2342696
  have htrace : WordTrace (prefixWord ++ tailWord_2342696) baseStart_2342696 baseEnd_2342696 := by
    simpa [prefixWord, tailWord_2342696, baseEnd_2342696] using wordTrace_append hprefix tailTrace_2342696
  have hstable : (prefixWord ++ tailWord_2342696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342696).length < 2 ^ (prefixWord ++ tailWord_2342696).sum := by decide
  have hdescent : baseEnd_2342696 < baseStart_2342696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342737 : List Nat := [1, 2, 2, 1, 5, 1, 1, 4, 5]
def baseStart_2342737 : Nat := 118140960795 + 2342737 * 2 ^ 59
def prefixEnd_2342737 : Nat := 4983230072969 + 3 ^ 40 * 2342737 * 2
def baseEnd_2342737 : Nat := 267322250682734614314101

theorem tailTrace_2342737 : CollatzResearch.WordTrace tailWord_2342737 prefixEnd_2342737 267322250682734614314101 := by
  unfold tailWord_2342737
  simp only [CollatzResearch.WordTrace]
  refine ⟨85446638113671431470514465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56964425409114287647009643 85446638113671431470514465)
  ·
    refine ⟨64084978585253573602885849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85446638113671431470514465 64084978585253573602885849)
    ·
      refine ⟨48063733938940180202164387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64084978585253573602885849 48063733938940180202164387)
      ·
        refine ⟨72095600908410270303246581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48063733938940180202164387 72095600908410270303246581)
        ·
          refine ⟨6758962585163462840929367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72095600908410270303246581 6758962585163462840929367)
          ·
            refine ⟨10138443877745194261394051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6758962585163462840929367 10138443877745194261394051)
            ·
              refine ⟨15207665816617791392091077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10138443877745194261394051 15207665816617791392091077)
              ·
                refine ⟨2851437340615835886017077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15207665816617791392091077 2851437340615835886017077)
                ·
                  refine ⟨267322250682734614314101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2851437340615835886017077 267322250682734614314101)
                  ·
                    rfl

theorem cell22_2342737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_2342737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342737 prefixEnd_2342737 := by exact prefixLift 2342737
  have htrace : WordTrace (prefixWord ++ tailWord_2342737) baseStart_2342737 baseEnd_2342737 := by
    simpa [prefixWord, tailWord_2342737, baseEnd_2342737] using wordTrace_append hprefix tailTrace_2342737
  have hstable : (prefixWord ++ tailWord_2342737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342737).length < 2 ^ (prefixWord ++ tailWord_2342737).sum := by decide
  have hdescent : baseEnd_2342737 < baseStart_2342737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342741 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2342741 : Nat := 118140960795 + 2342741 * 2 ^ 59
def prefixEnd_2342741 : Nat := 4983230072969 + 3 ^ 40 * 2342741 * 2
def baseEnd_2342741 : Nat := 801968121329949165842291

theorem tailTrace_2342741 : CollatzResearch.WordTrace tailWord_2342741 prefixEnd_2342741 801968121329949165842291 := by
  unfold tailWord_2342741
  simp only [CollatzResearch.WordTrace]
  refine ⟨85446784005656940153660077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56964522670437960102440051 85446784005656940153660077)
  ·
    refine ⟨32042544002121352557622529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85446784005656940153660077 32042544002121352557622529)
    ·
      refine ⟨24031908001591014418216897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32042544002121352557622529 24031908001591014418216897)
      ·
        refine ⟨18023931001193260813662673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24031908001591014418216897 18023931001193260813662673)
        ·
          refine ⟨13517948250894945610247005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18023931001193260813662673 13517948250894945610247005)
          ·
            refine ⟨5069230594085604603842627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13517948250894945610247005 5069230594085604603842627)
            ·
              refine ⟨7603845891128406905763941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069230594085604603842627 7603845891128406905763941)
              ·
                refine ⟨1425721104586576294830739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7603845891128406905763941 1425721104586576294830739)
                ·
                  refine ⟨2138581656879864442246109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425721104586576294830739 2138581656879864442246109)
                  ·
                    refine ⟨801968121329949165842291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138581656879864442246109 801968121329949165842291)
                    ·
                      rfl

theorem cell22_2342741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2342741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342741 prefixEnd_2342741 := by exact prefixLift 2342741
  have htrace : WordTrace (prefixWord ++ tailWord_2342741) baseStart_2342741 baseEnd_2342741 := by
    simpa [prefixWord, tailWord_2342741, baseEnd_2342741] using wordTrace_append hprefix tailTrace_2342741
  have hstable : (prefixWord ++ tailWord_2342741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342741).length < 2 ^ (prefixWord ++ tailWord_2342741).sum := by decide
  have hdescent : baseEnd_2342741 < baseStart_2342741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342752 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_2342752 : Nat := 118140960795 + 2342752 * 2 ^ 59
def prefixEnd_2342752 : Nat := 4983230072969 + 3 ^ 40 * 2342752 * 2
def baseEnd_2342752 : Nat := 801971886854748803817257

theorem tailTrace_2342752 : CollatzResearch.WordTrace tailWord_2342752 prefixEnd_2342752 801971886854748803817257 := by
  unfold tailWord_2342752
  simp only [CollatzResearch.WordTrace]
  refine ⟨42723592604308544516155255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56964790139078059354873673 42723592604308544516155255)
  ·
    refine ⟨64085388906462816774232883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42723592604308544516155255 64085388906462816774232883)
    ·
      refine ⟨96128083359694225161349325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64085388906462816774232883 96128083359694225161349325)
      ·
        refine ⟨36048031259885334435505997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96128083359694225161349325 36048031259885334435505997)
        ·
          refine ⟨13518011722457000413314749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36048031259885334435505997 13518011722457000413314749)
          ·
            refine ⟨5069254395921375154993031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13518011722457000413314749 5069254395921375154993031)
            ·
              refine ⟨7603881593882062732489547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069254395921375154993031 7603881593882062732489547)
              ·
                refine ⟨11405822390823094098734321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7603881593882062732489547 11405822390823094098734321)
                ·
                  refine ⟨8554366793117320574050741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11405822390823094098734321 8554366793117320574050741)
                  ·
                    refine ⟨801971886854748803817257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8554366793117320574050741 801971886854748803817257)
                    ·
                      rfl

theorem cell22_2342752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_2342752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342752 prefixEnd_2342752 := by exact prefixLift 2342752
  have htrace : WordTrace (prefixWord ++ tailWord_2342752) baseStart_2342752 baseEnd_2342752 := by
    simpa [prefixWord, tailWord_2342752, baseEnd_2342752] using wordTrace_append hprefix tailTrace_2342752
  have hstable : (prefixWord ++ tailWord_2342752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342752).length < 2 ^ (prefixWord ++ tailWord_2342752).sum := by decide
  have hdescent : baseEnd_2342752 < baseStart_2342752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342754 : List Nat := [3, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2342754 : Nat := 118140960795 + 2342754 * 2 ^ 59
def prefixEnd_2342754 : Nat := 4983230072969 + 3 ^ 40 * 2342754 * 2
def baseEnd_2342754 : Nat := 267324190498540488422417

theorem tailTrace_2342754 : CollatzResearch.WordTrace tailWord_2342754 prefixEnd_2342754 267324190498540488422417 := by
  unfold tailWord_2342754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21361814538652460843470829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56964838769739895582588877 21361814538652460843470829)
  ·
    refine ⟨8010680451994672816301561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21361814538652460843470829 8010680451994672816301561)
    ·
      refine ⟨6008010338996004612226171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010680451994672816301561 6008010338996004612226171)
      ·
        refine ⟨9012015508494006918339257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6008010338996004612226171 9012015508494006918339257)
        ·
          refine ⟨6759011631370505188754443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9012015508494006918339257 6759011631370505188754443)
          ·
            refine ⟨10138517447055757783131665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759011631370505188754443 10138517447055757783131665)
            ·
              refine ⟨7603888085291818337348749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10138517447055757783131665 7603888085291818337348749)
              ·
                refine ⟨2851458031984431876505781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7603888085291818337348749 2851458031984431876505781)
                ·
                  refine ⟨267324190498540488422417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2851458031984431876505781 267324190498540488422417)
                  ·
                    rfl

theorem cell22_2342754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2342754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342754 prefixEnd_2342754 := by exact prefixLift 2342754
  have htrace : WordTrace (prefixWord ++ tailWord_2342754) baseStart_2342754 baseEnd_2342754 := by
    simpa [prefixWord, tailWord_2342754, baseEnd_2342754] using wordTrace_append hprefix tailTrace_2342754
  have hstable : (prefixWord ++ tailWord_2342754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342754).length < 2 ^ (prefixWord ++ tailWord_2342754).sum := by decide
  have hdescent : baseEnd_2342754 < baseStart_2342754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342910 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_2342910 : Nat := 118140960795 + 2342910 * 2 ^ 59
def prefixEnd_2342910 : Nat := 4983230072969 + 3 ^ 40 * 2342910 * 2
def baseEnd_2342910 : Nat := 802025973483689058366773

theorem tailTrace_2342910 : CollatzResearch.WordTrace tailWord_2342910 prefixEnd_2342910 802025973483689058366773 := by
  unfold tailWord_2342910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10681618492755585252070273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56968631961363121344374789 10681618492755585252070273)
  ·
    refine ⟨8011213869566688939052705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10681618492755585252070273 8011213869566688939052705)
    ·
      refine ⟨6008410402175016704289529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8011213869566688939052705 6008410402175016704289529)
      ·
        refine ⟨4506307801631262528217147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008410402175016704289529 4506307801631262528217147)
        ·
          refine ⟨6759461702446893792325721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506307801631262528217147 6759461702446893792325721)
          ·
            refine ⟨5069596276835170344244291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6759461702446893792325721 5069596276835170344244291)
            ·
              refine ⟨7604394415252755516366437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5069596276835170344244291 7604394415252755516366437)
              ·
                refine ⟨1425823952859891659318707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7604394415252755516366437 1425823952859891659318707)
                ·
                  refine ⟨2138735929289837488978061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425823952859891659318707 2138735929289837488978061)
                  ·
                    refine ⟨802025973483689058366773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138735929289837488978061 802025973483689058366773)
                    ·
                      rfl

theorem cell22_2342910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_2342910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342910 prefixEnd_2342910 := by exact prefixLift 2342910
  have htrace : WordTrace (prefixWord ++ tailWord_2342910) baseStart_2342910 baseEnd_2342910 := by
    simpa [prefixWord, tailWord_2342910, baseEnd_2342910] using wordTrace_append hprefix tailTrace_2342910
  have hstable : (prefixWord ++ tailWord_2342910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342910).length < 2 ^ (prefixWord ++ tailWord_2342910).sum := by decide
  have hdescent : baseEnd_2342910 < baseStart_2342910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342919 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2342919 : Nat := 118140960795 + 2342919 * 2 ^ 59
def prefixEnd_2342919 : Nat := 4983230072969 + 3 ^ 40 * 2342919 * 2
def baseEnd_2342919 : Nat := 802029054367616034891745

theorem tailTrace_2342919 : CollatzResearch.WordTrace tailWord_2342919 prefixEnd_2342919 802029054367616034891745 := by
  unfold tailWord_2342919
  simp only [CollatzResearch.WordTrace]
  refine ⟨85453276199012076553639811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56968850799341384369093207 85453276199012076553639811)
  ·
    refine ⟨128179914298518114830459717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85453276199012076553639811 128179914298518114830459717)
    ·
      refine ⟨24033733930972146530711197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128179914298518114830459717 24033733930972146530711197)
      ·
        refine ⟨9012650224114554949016699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24033733930972146530711197 9012650224114554949016699)
        ·
          refine ⟨13518975336171832423525049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9012650224114554949016699 13518975336171832423525049)
          ·
            refine ⟨10139231502128874317643787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13518975336171832423525049 10139231502128874317643787)
            ·
              refine ⟨15208847253193311476465681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10139231502128874317643787 15208847253193311476465681)
              ·
                refine ⟨11406635439894983607349261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15208847253193311476465681 11406635439894983607349261)
                ·
                  refine ⟨4277488289960618852755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11406635439894983607349261 4277488289960618852755973)
                  ·
                    refine ⟨802029054367616034891745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4277488289960618852755973 802029054367616034891745)
                    ·
                      rfl

theorem cell22_2342919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2342919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342919 prefixEnd_2342919 := by exact prefixLift 2342919
  have htrace : WordTrace (prefixWord ++ tailWord_2342919) baseStart_2342919 baseEnd_2342919 := by
    simpa [prefixWord, tailWord_2342919, baseEnd_2342919] using wordTrace_append hprefix tailTrace_2342919
  have hstable : (prefixWord ++ tailWord_2342919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342919).length < 2 ^ (prefixWord ++ tailWord_2342919).sum := by decide
  have hdescent : baseEnd_2342919 < baseStart_2342919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342949 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2342949 : Nat := 118140960795 + 2342949 * 2 ^ 59
def prefixEnd_2342949 : Nat := 4983230072969 + 3 ^ 40 * 2342949 * 2
def baseEnd_2342949 : Nat := 802039323980705956641653

theorem tailTrace_2342949 : CollatzResearch.WordTrace tailWord_2342949 prefixEnd_2342949 802039323980705956641653 := by
  unfold tailWord_2342949
  simp only [CollatzResearch.WordTrace]
  refine ⟨85454370388903391677231901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56969580259268927784821267 85454370388903391677231901)
  ·
    refine ⟨32045388895838771878961963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85454370388903391677231901 32045388895838771878961963)
    ·
      refine ⟨48068083343758157818442945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32045388895838771878961963 48068083343758157818442945)
      ·
        refine ⟨36051062507818618363832209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48068083343758157818442945 36051062507818618363832209)
        ·
          refine ⟨27038296880863963772874157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36051062507818618363832209 27038296880863963772874157)
          ·
            refine ⟨10139361330323986414827809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27038296880863963772874157 10139361330323986414827809)
            ·
              refine ⟨7604520997742989811120857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10139361330323986414827809 7604520997742989811120857)
              ·
                refine ⟨5703390748307242358340643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7604520997742989811120857 5703390748307242358340643)
                ·
                  refine ⟨8555086122460863537510965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5703390748307242358340643 8555086122460863537510965)
                  ·
                    refine ⟨802039323980705956641653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8555086122460863537510965 802039323980705956641653)
                    ·
                      rfl

theorem cell22_2342949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2342949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342949 prefixEnd_2342949 := by exact prefixLift 2342949
  have htrace : WordTrace (prefixWord ++ tailWord_2342949) baseStart_2342949 baseEnd_2342949 := by
    simpa [prefixWord, tailWord_2342949, baseEnd_2342949] using wordTrace_append hprefix tailTrace_2342949
  have hstable : (prefixWord ++ tailWord_2342949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342949).length < 2 ^ (prefixWord ++ tailWord_2342949).sum := by decide
  have hdescent : baseEnd_2342949 < baseStart_2342949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342983 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 2, 3]
def baseStart_2342983 : Nat := 118140960795 + 2342983 * 2 ^ 59
def prefixEnd_2342983 : Nat := 4983230072969 + 3 ^ 40 * 2342983 * 2
def baseEnd_2342983 : Nat := 802050962875541201291549

theorem tailTrace_2342983 : CollatzResearch.WordTrace tailWord_2342983 prefixEnd_2342983 802050962875541201291549 := by
  unfold tailWord_2342983
  simp only [CollatzResearch.WordTrace]
  refine ⟨85455610470780215483969603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56970406980520143655979735 85455610470780215483969603)
  ·
    refine ⟨128183415706170323225954405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85455610470780215483969603 128183415706170323225954405)
    ·
      refine ⟨24034390444906935604866451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128183415706170323225954405 24034390444906935604866451)
      ·
        refine ⟨36051585667360403407299677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24034390444906935604866451 36051585667360403407299677)
        ·
          refine ⟨13519344625260151277737379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36051585667360403407299677 13519344625260151277737379)
          ·
            refine ⟨20279016937890226916606069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13519344625260151277737379 20279016937890226916606069)
            ·
              refine ⟨1901157837927208773431819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20279016937890226916606069 1901157837927208773431819)
              ·
                refine ⟨2851736756890813160147729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1901157837927208773431819 2851736756890813160147729)
                ·
                  refine ⟨2138802567668109870110797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2851736756890813160147729 2138802567668109870110797)
                  ·
                    refine ⟨802050962875541201291549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138802567668109870110797 802050962875541201291549)
                    ·
                      rfl

theorem cell22_2342983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_2342983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342983 prefixEnd_2342983 := by exact prefixLift 2342983
  have htrace : WordTrace (prefixWord ++ tailWord_2342983) baseStart_2342983 baseEnd_2342983 := by
    simpa [prefixWord, tailWord_2342983, baseEnd_2342983] using wordTrace_append hprefix tailTrace_2342983
  have hstable : (prefixWord ++ tailWord_2342983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342983).length < 2 ^ (prefixWord ++ tailWord_2342983).sum := by decide
  have hdescent : baseEnd_2342983 < baseStart_2342983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2342998 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2342998 : Nat := 118140960795 + 2342998 * 2 ^ 59
def prefixEnd_2342998 : Nat := 4983230072969 + 3 ^ 40 * 2342998 * 2
def baseEnd_2342998 : Nat := 802056097682086162166503

theorem tailTrace_2342998 : CollatzResearch.WordTrace tailWord_2342998 prefixEnd_2342998 802056097682086162166503 := by
  unfold tailWord_2342998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341009847857867065360353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56970771710483915363843765 5341009847857867065360353)
  ·
    refine ⟨4005757385893400299020265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5341009847857867065360353 4005757385893400299020265)
    ·
      refine ⟨3004318039420050224265199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4005757385893400299020265 3004318039420050224265199)
      ·
        refine ⟨4506477059130075336397799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3004318039420050224265199 4506477059130075336397799)
        ·
          refine ⟨6759715588695113004596699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4506477059130075336397799 6759715588695113004596699)
          ·
            refine ⟨10139573383042669506895049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6759715588695113004596699 10139573383042669506895049)
            ·
              refine ⟨7604680037282002130171287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10139573383042669506895049 7604680037282002130171287)
              ·
                refine ⟨11407020055923003195256931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7604680037282002130171287 11407020055923003195256931)
                ·
                  refine ⟨17110530083884504792885397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11407020055923003195256931 17110530083884504792885397)
                  ·
                    refine ⟨802056097682086162166503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17110530083884504792885397 802056097682086162166503)
                    ·
                      rfl

theorem cell22_2342998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2342998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2342998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2342998 prefixEnd_2342998 := by exact prefixLift 2342998
  have htrace : WordTrace (prefixWord ++ tailWord_2342998) baseStart_2342998 baseEnd_2342998 := by
    simpa [prefixWord, tailWord_2342998, baseEnd_2342998] using wordTrace_append hprefix tailTrace_2342998
  have hstable : (prefixWord ++ tailWord_2342998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2342998).length < 2 ^ (prefixWord ++ tailWord_2342998).sum := by decide
  have hdescent : baseEnd_2342998 < baseStart_2342998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2342998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343024 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_2343024 : Nat := 118140960795 + 2343024 * 2 ^ 59
def prefixEnd_2343024 : Nat := 4983230072969 + 3 ^ 40 * 2343024 * 2
def baseEnd_2343024 : Nat := 267354999337810253672141

theorem tailTrace_2343024 : CollatzResearch.WordTrace tailWord_2343024 prefixEnd_2343024 267354999337810253672141 := by
  unfold tailWord_2343024
  simp only [CollatzResearch.WordTrace]
  refine ⟨42728552931815839743106063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56971403909087786324141417 42728552931815839743106063)
  ·
    refine ⟨64092829397723759614659095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42728552931815839743106063 64092829397723759614659095)
    ·
      refine ⟨96139244096585639421988643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64092829397723759614659095 96139244096585639421988643)
      ·
        refine ⟨144208866144878459132982965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96139244096585639421988643 144208866144878459132982965)
        ·
          refine ⟨13519581201082355543717153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144208866144878459132982965 13519581201082355543717153)
          ·
            refine ⟨10139685900811766657787865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13519581201082355543717153 10139685900811766657787865)
            ·
              refine ⟨7604764425608824993340899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10139685900811766657787865 7604764425608824993340899)
              ·
                refine ⟨11407146638413237490011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7604764425608824993340899 11407146638413237490011349)
                ·
                  refine ⟨267354999337810253672141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11407146638413237490011349 267354999337810253672141)
                  ·
                    rfl

theorem cell22_2343024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_2343024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343024 prefixEnd_2343024 := by exact prefixLift 2343024
  have htrace : WordTrace (prefixWord ++ tailWord_2343024) baseStart_2343024 baseEnd_2343024 := by
    simpa [prefixWord, tailWord_2343024, baseEnd_2343024] using wordTrace_append hprefix tailTrace_2343024
  have hstable : (prefixWord ++ tailWord_2343024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343024).length < 2 ^ (prefixWord ++ tailWord_2343024).sum := by decide
  have hdescent : baseEnd_2343024 < baseStart_2343024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343079 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2343079 : Nat := 118140960795 + 2343079 * 2 ^ 59
def prefixEnd_2343079 : Nat := 4983230072969 + 3 ^ 40 * 2343079 * 2
def baseEnd_2343079 : Nat := 802083825637428950891255

theorem tailTrace_2343079 : CollatzResearch.WordTrace tailWord_2343079 prefixEnd_2343079 802083825637428950891255 := by
  unfold tailWord_2343079
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459111878432423879464291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56972741252288282586309527 85459111878432423879464291)
  ·
    refine ⟨128188667817648635819196437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85459111878432423879464291 128188667817648635819196437)
    ·
      refine ⟨6008843803952279804024833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128188667817648635819196437 6008843803952279804024833)
      ·
        refine ⟨4506632852964209853018625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6008843803952279804024833 4506632852964209853018625)
        ·
          refine ⟨3379974639723157389763969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506632852964209853018625 3379974639723157389763969)
          ·
            refine ⟨2534980979792368042322977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379974639723157389763969 2534980979792368042322977)
            ·
              refine ⟨1901235734844276031742233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2534980979792368042322977 1901235734844276031742233)
              ·
                refine ⟨1425926801133207023806675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901235734844276031742233 1425926801133207023806675)
                ·
                  refine ⟨2138890201699810535710013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1425926801133207023806675 2138890201699810535710013)
                  ·
                    refine ⟨802083825637428950891255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138890201699810535710013 802083825637428950891255)
                    ·
                      rfl

theorem cell22_2343079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2343079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343079 prefixEnd_2343079 := by exact prefixLift 2343079
  have htrace : WordTrace (prefixWord ++ tailWord_2343079) baseStart_2343079 baseEnd_2343079 := by
    simpa [prefixWord, tailWord_2343079, baseEnd_2343079] using wordTrace_append hprefix tailTrace_2343079
  have hstable : (prefixWord ++ tailWord_2343079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343079).length < 2 ^ (prefixWord ++ tailWord_2343079).sum := by decide
  have hdescent : baseEnd_2343079 < baseStart_2343079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343099 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_2343099 : Nat := 118140960795 + 2343099 * 2 ^ 59
def prefixEnd_2343099 : Nat := 4983230072969 + 3 ^ 40 * 2343099 * 2
def baseEnd_2343099 : Nat := 802090672046155565391193

theorem tailTrace_2343099 : CollatzResearch.WordTrace tailWord_2343099 prefixEnd_2343099 802090672046155565391193 := by
  unfold tailWord_2343099
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459841338359967295192351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56973227558906644863461567 85459841338359967295192351)
  ·
    refine ⟨128189762007539950942788527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85459841338359967295192351 128189762007539950942788527)
    ·
      refine ⟨192284643011309926414182791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128189762007539950942788527 192284643011309926414182791)
      ·
        refine ⟨288426964516964889621274187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192284643011309926414182791 288426964516964889621274187)
        ·
          refine ⟨432640446775447334431911281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288426964516964889621274187 432640446775447334431911281)
          ·
            refine ⟨324480335081585500823933461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432640446775447334431911281 324480335081585500823933461)
            ·
              refine ⟨15210015706949320351121881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 324480335081585500823933461 15210015706949320351121881)
              ·
                refine ⟨11407511780211990263341411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15210015706949320351121881 11407511780211990263341411)
                ·
                  refine ⟨17111267670317985395012117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11407511780211990263341411 17111267670317985395012117)
                  ·
                    refine ⟨802090672046155565391193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17111267670317985395012117 802090672046155565391193)
                    ·
                      rfl

theorem cell22_2343099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_2343099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343099 prefixEnd_2343099 := by exact prefixLift 2343099
  have htrace : WordTrace (prefixWord ++ tailWord_2343099) baseStart_2343099 baseEnd_2343099 := by
    simpa [prefixWord, tailWord_2343099, baseEnd_2343099] using wordTrace_append hprefix tailTrace_2343099
  have hstable : (prefixWord ++ tailWord_2343099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343099).length < 2 ^ (prefixWord ++ tailWord_2343099).sum := by decide
  have hdescent : baseEnd_2343099 < baseStart_2343099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343101 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_2343101 : Nat := 118140960795 + 2343101 * 2 ^ 59
def prefixEnd_2343101 : Nat := 4983230072969 + 3 ^ 40 * 2343101 * 2
def baseEnd_2343101 : Nat := 802091356687028226841187

theorem tailTrace_2343101 : CollatzResearch.WordTrace tailWord_2343101 prefixEnd_2343101 802091356687028226841187 := by
  unfold tailWord_2343101
  simp only [CollatzResearch.WordTrace]
  refine ⟨85459914284352721636765157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56973276189568481091176771 85459914284352721636765157)
  ·
    refine ⟨16023733928316135306893467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85459914284352721636765157 16023733928316135306893467)
    ·
      refine ⟨24035600892474202960340201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16023733928316135306893467 24035600892474202960340201)
      ·
        refine ⟨18026700669355652220255151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24035600892474202960340201 18026700669355652220255151)
        ·
          refine ⟨27040051004033478330382727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18026700669355652220255151 27040051004033478330382727)
          ·
            refine ⟨40560076506050217495574091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27040051004033478330382727 40560076506050217495574091)
            ·
              refine ⟨60840114759075326243361137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40560076506050217495574091 60840114759075326243361137)
              ·
                refine ⟨45630086069306494682520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60840114759075326243361137 45630086069306494682520853)
                ·
                  refine ⟨2138910284498741938243165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45630086069306494682520853 2138910284498741938243165)
                  ·
                    refine ⟨802091356687028226841187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138910284498741938243165 802091356687028226841187)
                    ·
                      rfl

theorem cell22_2343101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_2343101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343101 prefixEnd_2343101 := by exact prefixLift 2343101
  have htrace : WordTrace (prefixWord ++ tailWord_2343101) baseStart_2343101 baseEnd_2343101 := by
    simpa [prefixWord, tailWord_2343101, baseEnd_2343101] using wordTrace_append hprefix tailTrace_2343101
  have hstable : (prefixWord ++ tailWord_2343101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343101).length < 2 ^ (prefixWord ++ tailWord_2343101).sum := by decide
  have hdescent : baseEnd_2343101 < baseStart_2343101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343159 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 11]
def baseStart_2343159 : Nat := 118140960795 + 2343159 * 2 ^ 59
def prefixEnd_2343159 : Nat := 4983230072969 + 3 ^ 40 * 2343159 * 2
def baseEnd_2343159 : Nat := 267370403757445136297003

theorem tailTrace_2343159 : CollatzResearch.WordTrace tailWord_2343159 prefixEnd_2343159 267370403757445136297003 := by
  unfold tailWord_2343159
  simp only [CollatzResearch.WordTrace]
  refine ⟨85462029718142597542376531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56974686478761731694917687 85462029718142597542376531)
  ·
    refine ⟨128193044577213896313564797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85462029718142597542376531 128193044577213896313564797)
    ·
      refine ⟨48072391716455211117586799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128193044577213896313564797 48072391716455211117586799)
      ·
        refine ⟨72108587574682816676380199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48072391716455211117586799 72108587574682816676380199)
        ·
          refine ⟨108162881362024225014570299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72108587574682816676380199 108162881362024225014570299)
          ·
            refine ⟨162244322043036337521855449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108162881362024225014570299 162244322043036337521855449)
            ·
              refine ⟨121683241532277253141391587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162244322043036337521855449 121683241532277253141391587)
              ·
                refine ⟨182524862298415879712087381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121683241532277253141391587 182524862298415879712087381)
                ·
                  refine ⟨267370403757445136297003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 182524862298415879712087381 267370403757445136297003)
                  ·
                    rfl

theorem cell22_2343159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_2343159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343159 prefixEnd_2343159 := by exact prefixLift 2343159
  have htrace : WordTrace (prefixWord ++ tailWord_2343159) baseStart_2343159 baseEnd_2343159 := by
    simpa [prefixWord, tailWord_2343159, baseEnd_2343159] using wordTrace_append hprefix tailTrace_2343159
  have hstable : (prefixWord ++ tailWord_2343159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343159).length < 2 ^ (prefixWord ++ tailWord_2343159).sum := by decide
  have hdescent : baseEnd_2343159 < baseStart_2343159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343176 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_2343176 : Nat := 118140960795 + 2343176 * 2 ^ 59
def prefixEnd_2343176 : Nat := 4983230072969 + 3 ^ 40 * 2343176 * 2
def baseEnd_2343176 : Nat := 267372343573251010405319

theorem tailTrace_2343176 : CollatzResearch.WordTrace tailWord_2343176 prefixEnd_2343176 267372343573251010405319 := by
  unfold tailWord_2343176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42731324879540504722872691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56975099839387339630496921 42731324879540504722872691)
  ·
    refine ⟨64096987319310757084309037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42731324879540504722872691 64096987319310757084309037)
    ·
      refine ⟨24036370244741533906615889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64096987319310757084309037 24036370244741533906615889)
      ·
        refine ⟨18027277683556150429961917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24036370244741533906615889 18027277683556150429961917)
        ·
          refine ⟨6760229131333556411235719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18027277683556150429961917 6760229131333556411235719)
          ·
            refine ⟨10140343697000334616853579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760229131333556411235719 10140343697000334616853579)
            ·
              refine ⟨15210515545500501925280369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10140343697000334616853579 15210515545500501925280369)
              ·
                refine ⟨11407886659125376443960277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15210515545500501925280369 11407886659125376443960277)
                ·
                  refine ⟨267372343573251010405319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11407886659125376443960277 267372343573251010405319)
                  ·
                    rfl

theorem cell22_2343176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_2343176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343176 prefixEnd_2343176 := by exact prefixLift 2343176
  have htrace : WordTrace (prefixWord ++ tailWord_2343176) baseStart_2343176 baseEnd_2343176 := by
    simpa [prefixWord, tailWord_2343176, baseEnd_2343176] using wordTrace_append hprefix tailTrace_2343176
  have hstable : (prefixWord ++ tailWord_2343176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343176).length < 2 ^ (prefixWord ++ tailWord_2343176).sum := by decide
  have hdescent : baseEnd_2343176 < baseStart_2343176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343197 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2343197 : Nat := 118140960795 + 2343197 * 2 ^ 59
def prefixEnd_2343197 : Nat := 4983230072969 + 3 ^ 40 * 2343197 * 2
def baseEnd_2343197 : Nat := 802124219448915976440893

theorem tailTrace_2343197 : CollatzResearch.WordTrace tailWord_2343197 prefixEnd_2343197 802124219448915976440893 := by
  unfold tailWord_2343197
  simp only [CollatzResearch.WordTrace]
  refine ⟨85463415692004930032259845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56975610461336620021506563 85463415692004930032259845)
  ·
    refine ⟨16024390442250924381048721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85463415692004930032259845 16024390442250924381048721)
    ·
      refine ⟨12018292831688193285786541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16024390442250924381048721 12018292831688193285786541)
      ·
        refine ⟨4506859811883072482169953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12018292831688193285786541 4506859811883072482169953)
        ·
          refine ⟨3380144858912304361627465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506859811883072482169953 3380144858912304361627465)
          ·
            refine ⟨2535108644184228271220599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3380144858912304361627465 2535108644184228271220599)
            ·
              refine ⟨3802662966276342406830899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535108644184228271220599 3802662966276342406830899)
              ·
                refine ⟨5703994449414513610246349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802662966276342406830899 5703994449414513610246349)
                ·
                  refine ⟨2138997918530442603842381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5703994449414513610246349 2138997918530442603842381)
                  ·
                    refine ⟨802124219448915976440893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2138997918530442603842381 802124219448915976440893)
                    ·
                      rfl

theorem cell22_2343197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2343197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343197 prefixEnd_2343197 := by exact prefixLift 2343197
  have htrace : WordTrace (prefixWord ++ tailWord_2343197) baseStart_2343197 baseEnd_2343197 := by
    simpa [prefixWord, tailWord_2343197, baseEnd_2343197] using wordTrace_append hprefix tailTrace_2343197
  have hstable : (prefixWord ++ tailWord_2343197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343197).length < 2 ^ (prefixWord ++ tailWord_2343197).sum := by decide
  have hdescent : baseEnd_2343197 < baseStart_2343197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343210 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_2343210 : Nat := 118140960795 + 2343210 * 2 ^ 59
def prefixEnd_2343210 : Nat := 4983230072969 + 3 ^ 40 * 2343210 * 2
def baseEnd_2343210 : Nat := 267376223204862758621951

theorem tailTrace_2343210 : CollatzResearch.WordTrace tailWord_2343210 prefixEnd_2343210 267376223204862758621951 := by
  unfold tailWord_2343210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21365972460239458313120771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56975926560638555501655389 21365972460239458313120771)
  ·
    refine ⟨32048958690359187469681157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21365972460239458313120771 32048958690359187469681157)
    ·
      refine ⟨6009179754442347650565217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32048958690359187469681157 6009179754442347650565217)
      ·
        refine ⟨4506884815831760737923913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6009179754442347650565217 4506884815831760737923913)
        ·
          refine ⟨3380163611873820553442935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4506884815831760737923913 3380163611873820553442935)
          ·
            refine ⟨5070245417810730830164403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380163611873820553442935 5070245417810730830164403)
            ·
              refine ⟨7605368126716096245246605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5070245417810730830164403 7605368126716096245246605)
              ·
                refine ⟨2852013047518536091967477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7605368126716096245246605 2852013047518536091967477)
                ·
                  refine ⟨267376223204862758621951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852013047518536091967477 267376223204862758621951)
                  ·
                    rfl

theorem cell22_2343210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_2343210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343210 prefixEnd_2343210 := by exact prefixLift 2343210
  have htrace : WordTrace (prefixWord ++ tailWord_2343210) baseStart_2343210 baseEnd_2343210 := by
    simpa [prefixWord, tailWord_2343210, baseEnd_2343210] using wordTrace_append hprefix tailTrace_2343210
  have hstable : (prefixWord ++ tailWord_2343210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343210).length < 2 ^ (prefixWord ++ tailWord_2343210).sum := by decide
  have hdescent : baseEnd_2343210 < baseStart_2343210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343221 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 8]
def baseStart_2343221 : Nat := 118140960795 + 2343221 * 2 ^ 59
def prefixEnd_2343221 : Nat := 4983230072969 + 3 ^ 40 * 2343221 * 2
def baseEnd_2343221 : Nat := 267377478379795971280273

theorem tailTrace_2343221 : CollatzResearch.WordTrace tailWord_2343221 prefixEnd_2343221 267377478379795971280273 := by
  unfold tailWord_2343221
  simp only [CollatzResearch.WordTrace]
  refine ⟨85464291043917982131133517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56976194029278654754089011 85464291043917982131133517)
  ·
    refine ⟨32049109141469243299175069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85464291043917982131133517 32049109141469243299175069)
    ·
      refine ⟨12018415928050966237190651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32049109141469243299175069 12018415928050966237190651)
      ·
        refine ⟨18027623892076449355785977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12018415928050966237190651 18027623892076449355785977)
        ·
          refine ⟨13520717919057337016839483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18027623892076449355785977 13520717919057337016839483)
          ·
            refine ⟨20281076878586005525259225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13520717919057337016839483 20281076878586005525259225)
            ·
              refine ⟨15210807658939504143944419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20281076878586005525259225 15210807658939504143944419)
              ·
                refine ⟨22816211488409256215916629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15210807658939504143944419 22816211488409256215916629)
                ·
                  refine ⟨267377478379795971280273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22816211488409256215916629 267377478379795971280273)
                  ·
                    rfl

theorem cell22_2343221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_2343221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343221 prefixEnd_2343221 := by exact prefixLift 2343221
  have htrace : WordTrace (prefixWord ++ tailWord_2343221) baseStart_2343221 baseEnd_2343221 := by
    simpa [prefixWord, tailWord_2343221, baseEnd_2343221] using wordTrace_append hprefix tailTrace_2343221
  have hstable : (prefixWord ++ tailWord_2343221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343221).length < 2 ^ (prefixWord ++ tailWord_2343221).sum := by decide
  have hdescent : baseEnd_2343221 < baseStart_2343221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343251 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_2343251 : Nat := 118140960795 + 2343251 * 2 ^ 59
def prefixEnd_2343251 : Nat := 4983230072969 + 3 ^ 40 * 2343251 * 2
def baseEnd_2343251 : Nat := 802142704752477835590727

theorem tailTrace_2343251 : CollatzResearch.WordTrace tailWord_2343251 prefixEnd_2343251 802142704752477835590727 := by
  unfold tailWord_2343251
  simp only [CollatzResearch.WordTrace]
  refine ⟨85465385233809297254725607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56976923489206198169817071 85465385233809297254725607)
  ·
    refine ⟨128198077850713945882088411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85465385233809297254725607 128198077850713945882088411)
    ·
      refine ⟨192297116776070918823132617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128198077850713945882088411 192297116776070918823132617)
      ·
        refine ⟨144222837582053189117349463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192297116776070918823132617 144222837582053189117349463)
        ·
          refine ⟨216334256373079783676024195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144222837582053189117349463 216334256373079783676024195)
          ·
            refine ⟨324501384559619675514036293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216334256373079783676024195 324501384559619675514036293)
            ·
              refine ⟨60844009604928689158881805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 324501384559619675514036293 60844009604928689158881805)
              ·
                refine ⟨22816503601848258434580677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60844009604928689158881805 22816503601848258434580677)
                ·
                  refine ⟨4278094425346548456483877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22816503601848258434580677 4278094425346548456483877)
                  ·
                    refine ⟨802142704752477835590727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278094425346548456483877 802142704752477835590727)
                    ·
                      rfl

theorem cell22_2343251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_2343251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343251 prefixEnd_2343251 := by exact prefixLift 2343251
  have htrace : WordTrace (prefixWord ++ tailWord_2343251) baseStart_2343251 baseEnd_2343251 := by
    simpa [prefixWord, tailWord_2343251, baseEnd_2343251] using wordTrace_append hprefix tailTrace_2343251
  have hstable : (prefixWord ++ tailWord_2343251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343251).length < 2 ^ (prefixWord ++ tailWord_2343251).sum := by decide
  have hdescent : baseEnd_2343251 < baseStart_2343251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343285 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2343285 : Nat := 118140960795 + 2343285 * 2 ^ 59
def prefixEnd_2343285 : Nat := 4983230072969 + 3 ^ 40 * 2343285 * 2
def baseEnd_2343285 : Nat := 802154343647313080240623

theorem tailTrace_2343285 : CollatzResearch.WordTrace tailWord_2343285 prefixEnd_2343285 802154343647313080240623 := by
  unfold tailWord_2343285
  simp only [CollatzResearch.WordTrace]
  refine ⟨85466625315686121061463309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56977750210457414040975539 85466625315686121061463309)
  ·
    refine ⟨32049984493382295398048741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85466625315686121061463309 32049984493382295398048741)
    ·
      refine ⟨6009372092509180387134139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32049984493382295398048741 6009372092509180387134139)
      ·
        refine ⟨9014058138763770580701209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6009372092509180387134139 9014058138763770580701209)
        ·
          refine ⟨6760543604072827935525907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9014058138763770580701209 6760543604072827935525907)
          ·
            refine ⟨10140815406109241903288861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760543604072827935525907 10140815406109241903288861)
            ·
              refine ⟨3802805777290965713733323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10140815406109241903288861 3802805777290965713733323)
              ·
                refine ⟨5704208665936448570599985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3802805777290965713733323 5704208665936448570599985)
                ·
                  refine ⟨4278156499452336427949989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5704208665936448570599985 4278156499452336427949989)
                  ·
                    refine ⟨802154343647313080240623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278156499452336427949989 802154343647313080240623)
                    ·
                      rfl

theorem cell22_2343285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2343285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343285 prefixEnd_2343285 := by exact prefixLift 2343285
  have htrace : WordTrace (prefixWord ++ tailWord_2343285) baseStart_2343285 baseEnd_2343285 := by
    simpa [prefixWord, tailWord_2343285, baseEnd_2343285] using wordTrace_append hprefix tailTrace_2343285
  have hstable : (prefixWord ++ tailWord_2343285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343285).length < 2 ^ (prefixWord ++ tailWord_2343285).sum := by decide
  have hdescent : baseEnd_2343285 < baseStart_2343285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343405 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_2343405 : Nat := 118140960795 + 2343405 * 2 ^ 59
def prefixEnd_2343405 : Nat := 4983230072969 + 3 ^ 40 * 2343405 * 2
def baseEnd_2343405 : Nat := 802195422099672767240255

theorem tailTrace_2343405 : CollatzResearch.WordTrace tailWord_2343405 prefixEnd_2343405 802195422099672767240255 := by
  unfold tailWord_2343405
  simp only [CollatzResearch.WordTrace]
  refine ⟨85471002075251381555831669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56980668050167587703887779 85471002075251381555831669)
  ·
    refine ⟨8012906444554817020859219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85471002075251381555831669 8012906444554817020859219)
    ·
      refine ⟨12019359666832225531288829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8012906444554817020859219 12019359666832225531288829)
      ·
        refine ⟨4507259875062084574233311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12019359666832225531288829 4507259875062084574233311)
        ·
          refine ⟨6760889812593126861349967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4507259875062084574233311 6760889812593126861349967)
          ·
            refine ⟨10141334718889690292024951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6760889812593126861349967 10141334718889690292024951)
            ·
              refine ⟨15212002078334535438037427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10141334718889690292024951 15212002078334535438037427)
              ·
                refine ⟨22818003117501803157056141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15212002078334535438037427 22818003117501803157056141)
                ·
                  refine ⟨8556751169063176183896053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22818003117501803157056141 8556751169063176183896053)
                  ·
                    refine ⟨802195422099672767240255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8556751169063176183896053 802195422099672767240255)
                    ·
                      rfl

theorem cell22_2343405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_2343405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343405 prefixEnd_2343405 := by exact prefixLift 2343405
  have htrace : WordTrace (prefixWord ++ tailWord_2343405) baseStart_2343405 baseEnd_2343405 := by
    simpa [prefixWord, tailWord_2343405, baseEnd_2343405] using wordTrace_append hprefix tailTrace_2343405
  have hstable : (prefixWord ++ tailWord_2343405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343405).length < 2 ^ (prefixWord ++ tailWord_2343405).sum := by decide
  have hdescent : baseEnd_2343405 < baseStart_2343405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343435 : List Nat := [1, 1, 1, 1, 7, 3, 1, 7]
def baseStart_2343435 : Nat := 118140960795 + 2343435 * 2 ^ 59
def prefixEnd_2343435 : Nat := 4983230072969 + 3 ^ 40 * 2343435 * 2
def baseEnd_2343435 : Nat := 89133965745862520998907

theorem tailTrace_2343435 : CollatzResearch.WordTrace tailWord_2343435 prefixEnd_2343435 89133965745862520998907 := by
  unfold tailWord_2343435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85472096265142696679423759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56981397510095131119615839 85472096265142696679423759)
  ·
    refine ⟨128208144397714045019135639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85472096265142696679423759 128208144397714045019135639)
    ·
      refine ⟨192312216596571067528703459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128208144397714045019135639 192312216596571067528703459)
      ·
        refine ⟨288468324894856601293055189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192312216596571067528703459 288468324894856601293055189)
        ·
          refine ⟨6760976364723201592805981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 288468324894856601293055189 6760976364723201592805981)
          ·
            refine ⟨2535366136771200597302243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6760976364723201592805981 2535366136771200597302243)
            ·
              refine ⟨3803049205156800895953365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535366136771200597302243 3803049205156800895953365)
              ·
                refine ⟨89133965745862520998907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3803049205156800895953365 89133965745862520998907)
                ·
                  rfl

theorem cell22_2343435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 7].length) (baseStart_2343435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343435 prefixEnd_2343435 := by exact prefixLift 2343435
  have htrace : WordTrace (prefixWord ++ tailWord_2343435) baseStart_2343435 baseEnd_2343435 := by
    simpa [prefixWord, tailWord_2343435, baseEnd_2343435] using wordTrace_append hprefix tailTrace_2343435
  have hstable : (prefixWord ++ tailWord_2343435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343435).length < 2 ^ (prefixWord ++ tailWord_2343435).sum := by decide
  have hdescent : baseEnd_2343435 < baseStart_2343435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343450 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_2343450 : Nat := 118140960795 + 2343450 * 2 ^ 59
def prefixEnd_2343450 : Nat := 4983230072969 + 3 ^ 40 * 2343450 * 2
def baseEnd_2343450 : Nat := 802210826519307649865117

theorem tailTrace_2343450 : CollatzResearch.WordTrace tailWord_2343450 prefixEnd_2343450 802210826519307649865117 := by
  unfold tailWord_2343450
  simp only [CollatzResearch.WordTrace]
  refine ⟨21368160840022088560304951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56981762240058902827479869 21368160840022088560304951)
  ·
    refine ⟨32052241260033132840457427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21368160840022088560304951 32052241260033132840457427)
    ·
      refine ⟨48078361890049699260686141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32052241260033132840457427 48078361890049699260686141)
      ·
        refine ⟨18029385708768637222757303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48078361890049699260686141 18029385708768637222757303)
        ·
          refine ⟨27044078563152955834135955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18029385708768637222757303 27044078563152955834135955)
          ·
            refine ⟨40566117844729433751203933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27044078563152955834135955 40566117844729433751203933)
            ·
              refine ⟨15212294191773537656701475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40566117844729433751203933 15212294191773537656701475)
              ·
                refine ⟨22818441287660306485052213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15212294191773537656701475 22818441287660306485052213)
                ·
                  refine ⟨2139228870718153732973645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22818441287660306485052213 2139228870718153732973645)
                  ·
                    refine ⟨802210826519307649865117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139228870718153732973645 802210826519307649865117)
                    ·
                      rfl

theorem cell22_2343450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_2343450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343450 prefixEnd_2343450 := by exact prefixLift 2343450
  have htrace : WordTrace (prefixWord ++ tailWord_2343450) baseStart_2343450 baseEnd_2343450 := by
    simpa [prefixWord, tailWord_2343450, baseEnd_2343450] using wordTrace_append hprefix tailTrace_2343450
  have hstable : (prefixWord ++ tailWord_2343450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343450).length < 2 ^ (prefixWord ++ tailWord_2343450).sum := by decide
  have hdescent : baseEnd_2343450 < baseStart_2343450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343469 : List Nat := [1, 5, 4, 1, 1, 1, 9]
def baseStart_2343469 : Nat := 118140960795 + 2343469 * 2 ^ 59
def prefixEnd_2343469 : Nat := 4983230072969 + 3 ^ 40 * 2343469 * 2
def baseEnd_2343469 : Nat := 29711752985466590134817

theorem tailTrace_2343469 : CollatzResearch.WordTrace tailWord_2343469 prefixEnd_2343469 29711752985466590134817 := by
  unfold tailWord_2343469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85473336347019520486161461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56982224231346346990774307 85473336347019520486161461)
  ·
    refine ⟨8013125282533080045577637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85473336347019520486161461 8013125282533080045577637)
    ·
      refine ⟨1502460990474952508545807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8013125282533080045577637 1502460990474952508545807)
      ·
        refine ⟨2253691485712428762818711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1502460990474952508545807 2253691485712428762818711)
        ·
          refine ⟨3380537228568643144228067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2253691485712428762818711 3380537228568643144228067)
          ·
            refine ⟨5070805842852964716342101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380537228568643144228067 5070805842852964716342101)
            ·
              refine ⟨29711752985466590134817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5070805842852964716342101 29711752985466590134817)
              ·
                rfl

theorem cell22_2343469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 9].length) (baseStart_2343469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343469 prefixEnd_2343469 := by exact prefixLift 2343469
  have htrace : WordTrace (prefixWord ++ tailWord_2343469) baseStart_2343469 baseEnd_2343469 := by
    simpa [prefixWord, tailWord_2343469, baseEnd_2343469] using wordTrace_append hprefix tailTrace_2343469
  have hstable : (prefixWord ++ tailWord_2343469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343469).length < 2 ^ (prefixWord ++ tailWord_2343469).sum := by decide
  have hdescent : baseEnd_2343469 < baseStart_2343469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343484 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2343484 : Nat := 118140960795 + 2343484 * 2 ^ 59
def prefixEnd_2343484 : Nat := 4983230072969 + 3 ^ 40 * 2343484 * 2
def baseEnd_2343484 : Nat := 802222465414142894515013

theorem tailTrace_2343484 : CollatzResearch.WordTrace tailWord_2343484 prefixEnd_2343484 802222465414142894515013 := by
  unfold tailWord_2343484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42736941720982589023978753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56982588961310118698638337 42736941720982589023978753)
  ·
    refine ⟨32052706290736941767984065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42736941720982589023978753 32052706290736941767984065)
    ·
      refine ⟨24039529718052706325988049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32052706290736941767984065 24039529718052706325988049)
      ·
        refine ⟨18029647288539529744491037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24039529718052706325988049 18029647288539529744491037)
        ·
          refine ⟨6761117733202323654184139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18029647288539529744491037 6761117733202323654184139)
          ·
            refine ⟨10141676599803485481276209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761117733202323654184139 10141676599803485481276209)
            ·
              refine ⟨7606257449852614110957157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10141676599803485481276209 7606257449852614110957157)
              ·
                refine ⟨1426173271847365145804467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7606257449852614110957157 1426173271847365145804467)
                ·
                  refine ⟨2139259907771047718706701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426173271847365145804467 2139259907771047718706701)
                  ·
                    refine ⟨802222465414142894515013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139259907771047718706701 802222465414142894515013)
                    ·
                      rfl

theorem cell22_2343484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2343484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343484 prefixEnd_2343484 := by exact prefixLift 2343484
  have htrace : WordTrace (prefixWord ++ tailWord_2343484) baseStart_2343484 baseEnd_2343484 := by
    simpa [prefixWord, tailWord_2343484, baseEnd_2343484] using wordTrace_append hprefix tailTrace_2343484
  have hstable : (prefixWord ++ tailWord_2343484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343484).length < 2 ^ (prefixWord ++ tailWord_2343484).sum := by decide
  have hdescent : baseEnd_2343484 < baseStart_2343484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343495 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2343495 : Nat := 118140960795 + 2343495 * 2 ^ 59
def prefixEnd_2343495 : Nat := 4983230072969 + 3 ^ 40 * 2343495 * 2
def baseEnd_2343495 : Nat := 802226230938942532489979

theorem tailTrace_2343495 : CollatzResearch.WordTrace tailWord_2343495 prefixEnd_2343495 802226230938942532489979 := by
  unfold tailWord_2343495
  simp only [CollatzResearch.WordTrace]
  refine ⟨85474284644925326926607939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56982856429950217951071959 85474284644925326926607939)
  ·
    refine ⟨128211426967387990389911909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85474284644925326926607939 128211426967387990389911909)
    ·
      refine ⟨24039642556385248198108483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128211426967387990389911909 24039642556385248198108483)
      ·
        refine ⟨36059463834577872297162725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24039642556385248198108483 36059463834577872297162725)
        ·
          refine ⟨6761149468983351055718011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36059463834577872297162725 6761149468983351055718011)
          ·
            refine ⟨10141724203475026583577017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6761149468983351055718011 10141724203475026583577017)
            ·
              refine ⟨7606293152606269937682763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10141724203475026583577017 7606293152606269937682763)
              ·
                refine ⟨11409439728909404906524145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7606293152606269937682763 11409439728909404906524145)
                ·
                  refine ⟨8557079796682053679893109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11409439728909404906524145 8557079796682053679893109)
                  ·
                    refine ⟨802226230938942532489979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8557079796682053679893109 802226230938942532489979)
                    ·
                      rfl

theorem cell22_2343495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2343495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343495 prefixEnd_2343495 := by exact prefixLift 2343495
  have htrace : WordTrace (prefixWord ++ tailWord_2343495) baseStart_2343495 baseEnd_2343495 := by
    simpa [prefixWord, tailWord_2343495, baseEnd_2343495] using wordTrace_append hprefix tailTrace_2343495
  have hstable : (prefixWord ++ tailWord_2343495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343495).length < 2 ^ (prefixWord ++ tailWord_2343495).sum := by decide
  have hdescent : baseEnd_2343495 < baseStart_2343495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343602 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_2343602 : Nat := 118140960795 + 2343602 * 2 ^ 59
def prefixEnd_2343602 : Nat := 4983230072969 + 3 ^ 40 * 2343602 * 2
def baseEnd_2343602 : Nat := 802262859225629920064651

theorem tailTrace_2343602 : CollatzResearch.WordTrace tailWord_2343602 prefixEnd_2343602 802262859225629920064651 := by
  unfold tailWord_2343602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21369546813884421050188265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56985458170358456133835373 21369546813884421050188265)
  ·
    refine ⟨16027160110413315787641199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21369546813884421050188265 16027160110413315787641199)
    ·
      refine ⟨24040740165619973681461799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16027160110413315787641199 24040740165619973681461799)
      ·
        refine ⟨36061110248429960522192699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24040740165619973681461799 36061110248429960522192699)
        ·
          refine ⟨54091665372644940783289049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36061110248429960522192699 54091665372644940783289049)
          ·
            refine ⟨40568749029483705587466787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54091665372644940783289049 40568749029483705587466787)
            ·
              refine ⟨60853123544225558381200181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40568749029483705587466787 60853123544225558381200181)
              ·
                refine ⟨5704980332271146098237517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60853123544225558381200181 5704980332271146098237517)
                ·
                  refine ⟨2139367624601679786839069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5704980332271146098237517 2139367624601679786839069)
                  ·
                    refine ⟨802262859225629920064651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139367624601679786839069 802262859225629920064651)
                    ·
                      rfl

theorem cell22_2343602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_2343602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343602 prefixEnd_2343602 := by exact prefixLift 2343602
  have htrace : WordTrace (prefixWord ++ tailWord_2343602) baseStart_2343602 baseEnd_2343602 := by
    simpa [prefixWord, tailWord_2343602, baseEnd_2343602] using wordTrace_append hprefix tailTrace_2343602
  have hstable : (prefixWord ++ tailWord_2343602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343602).length < 2 ^ (prefixWord ++ tailWord_2343602).sum := by decide
  have hdescent : baseEnd_2343602 < baseStart_2343602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343649 : List Nat := [1, 2, 3, 1, 4, 3, 1, 2, 5]
def baseStart_2343649 : Nat := 118140960795 + 2343649 * 2 ^ 59
def prefixEnd_2343649 : Nat := 4983230072969 + 3 ^ 40 * 2343649 * 2
def baseEnd_2343649 : Nat := 267426316095379154713169

theorem tailTrace_2343649 : CollatzResearch.WordTrace tailWord_2343649 prefixEnd_2343649 267426316095379154713169 := by
  unfold tailWord_2343649
  simp only [CollatzResearch.WordTrace]
  refine ⟨85479901486367411227714001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56986600990911607485142667 85479901486367411227714001)
  ·
    refine ⟨64109926114775558420785501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85479901486367411227714001 64109926114775558420785501)
    ·
      refine ⟨24041222293040834407794563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64109926114775558420785501 24041222293040834407794563)
      ·
        refine ⟨36061833439561251611691845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24041222293040834407794563 36061833439561251611691845)
        ·
          refine ⟨6761593769917734677192221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36061833439561251611691845 6761593769917734677192221)
          ·
            refine ⟨2535597663719150503947083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6761593769917734677192221 2535597663719150503947083)
            ·
              refine ⟨3803396495578725755920625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535597663719150503947083 3803396495578725755920625)
              ·
                refine ⟨2852547371684044316940469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3803396495578725755920625 2852547371684044316940469)
                ·
                  refine ⟨267426316095379154713169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852547371684044316940469 267426316095379154713169)
                  ·
                    rfl

theorem cell22_2343649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_2343649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343649 prefixEnd_2343649 := by exact prefixLift 2343649
  have htrace : WordTrace (prefixWord ++ tailWord_2343649) baseStart_2343649 baseEnd_2343649 := by
    simpa [prefixWord, tailWord_2343649, baseEnd_2343649] using wordTrace_append hprefix tailTrace_2343649
  have hstable : (prefixWord ++ tailWord_2343649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343649).length < 2 ^ (prefixWord ++ tailWord_2343649).sum := by decide
  have hdescent : baseEnd_2343649 < baseStart_2343649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343711 : List Nat := [1, 1, 2, 4, 2, 3, 3, 2, 4]
def baseStart_2343711 : Nat := 118140960795 + 2343711 * 2 ^ 59
def prefixEnd_2343711 : Nat := 4983230072969 + 3 ^ 40 * 2343711 * 2
def baseEnd_2343711 : Nat := 267433390717729989696439

theorem tailTrace_2343711 : CollatzResearch.WordTrace tailWord_2343711 prefixEnd_2343711 267433390717729989696439 := by
  unfold tailWord_2343711
  simp only [CollatzResearch.WordTrace]
  refine ⟨85482162812142795816470987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56988108541428530544313991 85482162812142795816470987)
  ·
    refine ⟨128223244218214193724706481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85482162812142795816470987 128223244218214193724706481)
    ·
      refine ⟨96167433163660645293529861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128223244218214193724706481 96167433163660645293529861)
      ·
        refine ⟨18031393718186370992536849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96167433163660645293529861 18031393718186370992536849)
        ·
          refine ⟨13523545288639778244402637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18031393718186370992536849 13523545288639778244402637)
          ·
            refine ⟨5071329483239916841650989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13523545288639778244402637 5071329483239916841650989)
            ·
              refine ⟨1901748556214968815619121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5071329483239916841650989 1901748556214968815619121)
              ·
                refine ⟨1426311417161226611714341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901748556214968815619121 1426311417161226611714341)
                ·
                  refine ⟨267433390717729989696439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1426311417161226611714341 267433390717729989696439)
                  ·
                    rfl

theorem cell22_2343711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 2, 4].length) (baseStart_2343711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343711 prefixEnd_2343711 := by exact prefixLift 2343711
  have htrace : WordTrace (prefixWord ++ tailWord_2343711) baseStart_2343711 baseEnd_2343711 := by
    simpa [prefixWord, tailWord_2343711, baseEnd_2343711] using wordTrace_append hprefix tailTrace_2343711
  have hstable : (prefixWord ++ tailWord_2343711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343711).length < 2 ^ (prefixWord ++ tailWord_2343711).sum := by decide
  have hdescent : baseEnd_2343711 < baseStart_2343711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343741 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_2343741 : Nat := 118140960795 + 2343741 * 2 ^ 59
def prefixEnd_2343741 : Nat := 4983230072969 + 3 ^ 40 * 2343741 * 2
def baseEnd_2343741 : Nat := 802310441766279890839225

theorem tailTrace_2343741 : CollatzResearch.WordTrace tailWord_2343741 prefixEnd_2343741 802310441766279890839225 := by
  unfold tailWord_2343741
  simp only [CollatzResearch.WordTrace]
  refine ⟨85483257002034110940063077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56988838001356073960042051 85483257002034110940063077)
  ·
    refine ⟨16028110687881395801261827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85483257002034110940063077 16028110687881395801261827)
    ·
      refine ⟨24042166031822093701892741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16028110687881395801261827 24042166031822093701892741)
      ·
        refine ⟨4507906130966642569104889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24042166031822093701892741 4507906130966642569104889)
        ·
          refine ⟨3380929598224981926828667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4507906130966642569104889 3380929598224981926828667)
          ·
            refine ⟨5071394397337472890243001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380929598224981926828667 5071394397337472890243001)
            ·
              refine ⟨3803545798003104667682251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071394397337472890243001 3803545798003104667682251)
              ·
                refine ⟨5705318697004657001523377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803545798003104667682251 5705318697004657001523377)
                ·
                  refine ⟨4278989022753492751142533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5705318697004657001523377 4278989022753492751142533)
                  ·
                    refine ⟨802310441766279890839225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4278989022753492751142533 802310441766279890839225)
                    ·
                      rfl

theorem cell22_2343741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_2343741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343741 prefixEnd_2343741 := by exact prefixLift 2343741
  have htrace : WordTrace (prefixWord ++ tailWord_2343741) baseStart_2343741 baseEnd_2343741 := by
    simpa [prefixWord, tailWord_2343741, baseEnd_2343741] using wordTrace_append hprefix tailTrace_2343741
  have hstable : (prefixWord ++ tailWord_2343741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343741).length < 2 ^ (prefixWord ++ tailWord_2343741).sum := by decide
  have hdescent : baseEnd_2343741 < baseStart_2343741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343784 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_2343784 : Nat := 118140960795 + 2343784 * 2 ^ 59
def prefixEnd_2343784 : Nat := 4983230072969 + 3 ^ 40 * 2343784 * 2
def baseEnd_2343784 : Nat := 267441720515014037338031

theorem tailTrace_2343784 : CollatzResearch.WordTrace tailWord_2343784 prefixEnd_2343784 267441720515014037338031 := by
  unfold tailWord_2343784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742412670439164641939203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56989883560585552855918937 42742412670439164641939203)
  ·
    refine ⟨64113619005658746962908805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42742412670439164641939203 64113619005658746962908805)
    ·
      refine ⟨12021303563561015055545401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64113619005658746962908805 12021303563561015055545401)
      ·
        refine ⟨9015977672670761291659051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12021303563561015055545401 9015977672670761291659051)
        ·
          refine ⟨13523966509006141937488577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9015977672670761291659051 13523966509006141937488577)
          ·
            refine ⟨10142974881754606453116433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13523966509006141937488577 10142974881754606453116433)
            ·
              refine ⟨7607231161315954839837325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10142974881754606453116433 7607231161315954839837325)
              ·
                refine ⟨2852711685493483064938997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7607231161315954839837325 2852711685493483064938997)
                ·
                  refine ⟨267441720515014037338031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2852711685493483064938997 267441720515014037338031)
                  ·
                    rfl

theorem cell22_2343784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_2343784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343784 prefixEnd_2343784 := by exact prefixLift 2343784
  have htrace : WordTrace (prefixWord ++ tailWord_2343784) baseStart_2343784 baseEnd_2343784 := by
    simpa [prefixWord, tailWord_2343784, baseEnd_2343784] using wordTrace_append hprefix tailTrace_2343784
  have hstable : (prefixWord ++ tailWord_2343784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343784).length < 2 ^ (prefixWord ++ tailWord_2343784).sum := by decide
  have hdescent : baseEnd_2343784 < baseStart_2343784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343812 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_2343812 : Nat := 118140960795 + 2343812 * 2 ^ 59
def prefixEnd_2343812 : Nat := 4983230072969 + 3 ^ 40 * 2343812 * 2
def baseEnd_2343812 : Nat := 267444915505753124104669

theorem tailTrace_2343812 : CollatzResearch.WordTrace tailWord_2343812 prefixEnd_2343812 267444915505753124104669 := by
  unfold tailWord_2343812
  simp only [CollatzResearch.WordTrace]
  refine ⟨42742923292388445032948845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56990564389851260043931793 42742923292388445032948845)
  ·
    refine ⟨16028596234645666887355817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42742923292388445032948845 16028596234645666887355817)
    ·
      refine ⟨12021447175984250165516863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16028596234645666887355817 12021447175984250165516863)
      ·
        refine ⟨18032170763976375248275295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12021447175984250165516863 18032170763976375248275295)
        ·
          refine ⟨27048256145964562872412943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18032170763976375248275295 27048256145964562872412943)
          ·
            refine ⟨40572384218946844308619415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27048256145964562872412943 40572384218946844308619415)
            ·
              refine ⟨60858576328420266462929123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40572384218946844308619415 60858576328420266462929123)
              ·
                refine ⟨91287864492630399694393685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60858576328420266462929123 91287864492630399694393685)
                ·
                  refine ⟨267444915505753124104669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91287864492630399694393685 267444915505753124104669)
                  ·
                    rfl

theorem cell22_2343812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_2343812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343812 prefixEnd_2343812 := by exact prefixLift 2343812
  have htrace : WordTrace (prefixWord ++ tailWord_2343812) baseStart_2343812 baseEnd_2343812 := by
    simpa [prefixWord, tailWord_2343812, baseEnd_2343812] using wordTrace_append hprefix tailTrace_2343812
  have hstable : (prefixWord ++ tailWord_2343812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343812).length < 2 ^ (prefixWord ++ tailWord_2343812).sum := by decide
  have hdescent : baseEnd_2343812 < baseStart_2343812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343829 : List Nat := [1, 3, 2, 1, 1, 5, 2, 1, 6]
def baseStart_2343829 : Nat := 118140960795 + 2343829 * 2 ^ 59
def prefixEnd_2343829 : Nat := 4983230072969 + 3 ^ 40 * 2343829 * 2
def baseEnd_2343829 : Nat := 267446855321558998212985

theorem tailTrace_2343829 : CollatzResearch.WordTrace tailWord_2343829 prefixEnd_2343829 267446855321558998212985 := by
  unfold tailWord_2343829
  simp only [CollatzResearch.WordTrace]
  refine ⟨85486466625715301969266541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56990977750476867979511027 85486466625715301969266541)
  ·
    refine ⟨32057424984643238238474953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85486466625715301969266541 32057424984643238238474953)
    ·
      refine ⟨24043068738482428678856215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32057424984643238238474953 24043068738482428678856215)
      ·
        refine ⟨36064603107723643018284323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24043068738482428678856215 36064603107723643018284323)
        ·
          refine ⟨54096904661585464527426485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36064603107723643018284323 54096904661585464527426485)
          ·
            refine ⟨5071584812023637299446233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54096904661585464527426485 5071584812023637299446233)
            ·
              refine ⟨3803688609017727974584675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071584812023637299446233 3803688609017727974584675)
              ·
                refine ⟨5705532913526591961877013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803688609017727974584675 5705532913526591961877013)
                ·
                  refine ⟨267446855321558998212985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5705532913526591961877013 267446855321558998212985)
                  ·
                    rfl

theorem cell22_2343829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_2343829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343829 prefixEnd_2343829 := by exact prefixLift 2343829
  have htrace : WordTrace (prefixWord ++ tailWord_2343829) baseStart_2343829 baseEnd_2343829 := by
    simpa [prefixWord, tailWord_2343829, baseEnd_2343829] using wordTrace_append hprefix tailTrace_2343829
  have hstable : (prefixWord ++ tailWord_2343829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343829).length < 2 ^ (prefixWord ++ tailWord_2343829).sum := by decide
  have hdescent : baseEnd_2343829 < baseStart_2343829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343979 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_2343979 : Nat := 118140960795 + 2343979 * 2 ^ 59
def prefixEnd_2343979 : Nat := 4983230072969 + 3 ^ 40 * 2343979 * 2
def baseEnd_2343979 : Nat := 802391914030126603388495

theorem tailTrace_2343979 : CollatzResearch.WordTrace tailWord_2343979 prefixEnd_2343979 802391914030126603388495 := by
  unfold tailWord_2343979
  simp only [CollatzResearch.WordTrace]
  refine ⟨85491937575171877587226991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56994625050114585058151327 85491937575171877587226991)
  ·
    refine ⟨128237906362757816380840487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85491937575171877587226991 128237906362757816380840487)
    ·
      refine ⟨192356859544136724571260731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128237906362757816380840487 192356859544136724571260731)
      ·
        refine ⟨288535289316205086856891097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192356859544136724571260731 288535289316205086856891097)
        ·
          refine ⟨216401466987153815142668323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288535289316205086856891097 216401466987153815142668323)
          ·
            refine ⟨324602200480730722714002485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216401466987153815142668323 324602200480730722714002485)
            ·
              refine ⟨30431456295068505254437733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 324602200480730722714002485 30431456295068505254437733)
              ·
                refine ⟨5705898055325344735207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30431456295068505254437733 5705898055325344735207075)
                ·
                  refine ⟨8558847082988017102810613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705898055325344735207075 8558847082988017102810613)
                  ·
                    refine ⟨802391914030126603388495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8558847082988017102810613 802391914030126603388495)
                    ·
                      rfl

theorem cell22_2343979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_2343979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343979 prefixEnd_2343979 := by exact prefixLift 2343979
  have htrace : WordTrace (prefixWord ++ tailWord_2343979) baseStart_2343979 baseEnd_2343979 := by
    simpa [prefixWord, tailWord_2343979, baseEnd_2343979] using wordTrace_append hprefix tailTrace_2343979
  have hstable : (prefixWord ++ tailWord_2343979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343979).length < 2 ^ (prefixWord ++ tailWord_2343979).sum := by decide
  have hdescent : baseEnd_2343979 < baseStart_2343979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2343998 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2343998 : Nat := 118140960795 + 2343998 * 2 ^ 59
def prefixEnd_2343998 : Nat := 4983230072969 + 3 ^ 40 * 2343998 * 2
def baseEnd_2343998 : Nat := 267466139372805629054479

theorem tailTrace_2343998 : CollatzResearch.WordTrace tailWord_2343998 prefixEnd_2343998 267466139372805629054479 := by
  unfold tailWord_2343998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686578820262880479021081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56995087041402029221445765 10686578820262880479021081)
  ·
    refine ⟨8014934115197160359265811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10686578820262880479021081 8014934115197160359265811)
    ·
      refine ⟨12022401172795740538898717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014934115197160359265811 12022401172795740538898717)
      ·
        refine ⟨4508400439798402702087019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12022401172795740538898717 4508400439798402702087019)
        ·
          refine ⟨6762600659697604053130529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4508400439798402702087019 6762600659697604053130529)
          ·
            refine ⟨5071950494773203039847897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6762600659697604053130529 5071950494773203039847897)
            ·
              refine ⟨3803962871079902279885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5071950494773203039847897 3803962871079902279885923)
              ·
                refine ⟨5705944306619853419828885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803962871079902279885923 5705944306619853419828885)
                ·
                  refine ⟨267466139372805629054479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5705944306619853419828885 267466139372805629054479)
                  ·
                    rfl

theorem cell22_2343998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2343998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2343998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2343998 prefixEnd_2343998 := by exact prefixLift 2343998
  have htrace : WordTrace (prefixWord ++ tailWord_2343998) baseStart_2343998 baseEnd_2343998 := by
    simpa [prefixWord, tailWord_2343998, baseEnd_2343998] using wordTrace_append hprefix tailTrace_2343998
  have hstable : (prefixWord ++ tailWord_2343998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2343998).length < 2 ^ (prefixWord ++ tailWord_2343998).sum := by decide
  have hdescent : baseEnd_2343998 < baseStart_2343998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2343998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344013 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_2344013 : Nat := 118140960795 + 2344013 * 2 ^ 59
def prefixEnd_2344013 : Nat := 4983230072969 + 3 ^ 40 * 2344013 * 2
def baseEnd_2344013 : Nat := 802403552924961848038391

theorem tailTrace_2344013 : CollatzResearch.WordTrace tailWord_2344013 prefixEnd_2344013 802403552924961848038391 := by
  unfold tailWord_2344013
  simp only [CollatzResearch.WordTrace]
  refine ⟨85493177657048701393964693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56995451771365800929309795 85493177657048701393964693)
  ·
    refine ⟨4007492702674157877842095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85493177657048701393964693 4007492702674157877842095)
    ·
      refine ⟨6011239054011236816763143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4007492702674157877842095 6011239054011236816763143)
      ·
        refine ⟨9016858581016855225144715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6011239054011236816763143 9016858581016855225144715)
        ·
          refine ⟨13525287871525282837717073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9016858581016855225144715 13525287871525282837717073)
          ·
            refine ⟨10143965903643962128287805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13525287871525282837717073 10143965903643962128287805)
            ·
              refine ⟨3803987213866485798107927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10143965903643962128287805 3803987213866485798107927)
              ·
                refine ⟨5705980820799728697161891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3803987213866485798107927 5705980820799728697161891)
                ·
                  refine ⟨8558971231199593045742837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5705980820799728697161891 8558971231199593045742837)
                  ·
                    refine ⟨802403552924961848038391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8558971231199593045742837 802403552924961848038391)
                    ·
                      rfl

theorem cell22_2344013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_2344013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344013 prefixEnd_2344013 := by exact prefixLift 2344013
  have htrace : WordTrace (prefixWord ++ tailWord_2344013) baseStart_2344013 baseEnd_2344013 := by
    simpa [prefixWord, tailWord_2344013, baseEnd_2344013] using wordTrace_append hprefix tailTrace_2344013
  have hstable : (prefixWord ++ tailWord_2344013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344013).length < 2 ^ (prefixWord ++ tailWord_2344013).sum := by decide
  have hdescent : baseEnd_2344013 < baseStart_2344013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344024 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_2344024 : Nat := 118140960795 + 2344024 * 2 ^ 59
def prefixEnd_2344024 : Nat := 4983230072969 + 3 ^ 40 * 2344024 * 2
def baseEnd_2344024 : Nat := 802407318449761486013357

theorem tailTrace_2344024 : CollatzResearch.WordTrace tailWord_2344024 prefixEnd_2344024 802407318449761486013357 := by
  unfold tailWord_2344024
  simp only [CollatzResearch.WordTrace]
  refine ⟨42746789430004425136307563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56995719240005900181743417 42746789430004425136307563)
  ·
    refine ⟨64120184145006637704461345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42746789430004425136307563 64120184145006637704461345)
    ·
      refine ⟨48090138108754978278346009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64120184145006637704461345 48090138108754978278346009)
      ·
        refine ⟨36067603581566233708759507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48090138108754978278346009 36067603581566233708759507)
        ·
          refine ⟨54101405372349350563139261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36067603581566233708759507 54101405372349350563139261)
          ·
            refine ⟨20288027014631006461177223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54101405372349350563139261 20288027014631006461177223)
            ·
              refine ⟨30432040521946509691765835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20288027014631006461177223 30432040521946509691765835)
              ·
                refine ⟨45648060782919764537648753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30432040521946509691765835 45648060782919764537648753)
                ·
                  refine ⟨34236045587189823403236565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45648060782919764537648753 34236045587189823403236565)
                  ·
                    refine ⟨802407318449761486013357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34236045587189823403236565 802407318449761486013357)
                    ·
                      rfl

theorem cell22_2344024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_2344024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344024 prefixEnd_2344024 := by exact prefixLift 2344024
  have htrace : WordTrace (prefixWord ++ tailWord_2344024) baseStart_2344024 baseEnd_2344024 := by
    simpa [prefixWord, tailWord_2344024, baseEnd_2344024] using wordTrace_append hprefix tailTrace_2344024
  have hstable : (prefixWord ++ tailWord_2344024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344024).length < 2 ^ (prefixWord ++ tailWord_2344024).sum := by decide
  have hdescent : baseEnd_2344024 < baseStart_2344024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344152 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_2344152 : Nat := 118140960795 + 2344152 * 2 ^ 59
def prefixEnd_2344152 : Nat := 4983230072969 + 3 ^ 40 * 2344152 * 2
def baseEnd_2344152 : Nat := 802451135465611818812965

theorem tailTrace_2344152 : CollatzResearch.WordTrace tailWord_2344152 prefixEnd_2344152 802451135465611818812965 := by
  unfold tailWord_2344152
  simp only [CollatzResearch.WordTrace]
  refine ⟨42749123701772564066637355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56998831602363418755516473 42749123701772564066637355)
  ·
    refine ⟨64123685552658846099956033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42749123701772564066637355 64123685552658846099956033)
    ·
      refine ⟨48092764164494134574967025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64123685552658846099956033 48092764164494134574967025)
      ·
        refine ⟨36069573123370600931225269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48092764164494134574967025 36069573123370600931225269)
        ·
          refine ⟨3381522480315993837302369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36069573123370600931225269 3381522480315993837302369)
          ·
            refine ⟨2536141860236995377976777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3381522480315993837302369 2536141860236995377976777)
            ·
              refine ⟨1902106395177746533482583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536141860236995377976777 1902106395177746533482583)
              ·
                refine ⟨2853159592766619800223875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902106395177746533482583 2853159592766619800223875)
                ·
                  refine ⟨4279739389149929700335813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853159592766619800223875 4279739389149929700335813)
                  ·
                    refine ⟨802451135465611818812965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4279739389149929700335813 802451135465611818812965)
                    ·
                      rfl

theorem cell22_2344152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_2344152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344152 prefixEnd_2344152 := by exact prefixLift 2344152
  have htrace : WordTrace (prefixWord ++ tailWord_2344152) baseStart_2344152 baseEnd_2344152 := by
    simpa [prefixWord, tailWord_2344152, baseEnd_2344152] using wordTrace_append hprefix tailTrace_2344152
  have hstable : (prefixWord ++ tailWord_2344152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344152).length < 2 ^ (prefixWord ++ tailWord_2344152).sum := by decide
  have hdescent : baseEnd_2344152 < baseStart_2344152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344161 : List Nat := [1, 2, 3, 1, 3, 3, 9]
def baseStart_2344161 : Nat := 118140960795 + 2344161 * 2 ^ 59
def prefixEnd_2344161 : Nat := 4983230072969 + 3 ^ 40 * 2344161 * 2
def baseEnd_2344161 : Nat := 29720526531464399827331

theorem tailTrace_2344161 : CollatzResearch.WordTrace tailWord_2344161 prefixEnd_2344161 29720526531464399827331 := by
  unfold tailWord_2344161
  simp only [CollatzResearch.WordTrace]
  refine ⟨85498575660512522670352337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56999050440341681780234891 85498575660512522670352337)
  ·
    refine ⟨64123931745384392002764253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85498575660512522670352337 64123931745384392002764253)
    ·
      refine ⟨24046474404519147001036595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64123931745384392002764253 24046474404519147001036595)
      ·
        refine ⟨36069711606778720501554893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24046474404519147001036595 36069711606778720501554893)
        ·
          refine ⟨13526141852542020188083085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36069711606778720501554893 13526141852542020188083085)
          ·
            refine ⟨5072303194703257570531157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13526141852542020188083085 5072303194703257570531157)
            ·
              refine ⟨29720526531464399827331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5072303194703257570531157 29720526531464399827331)
              ·
                rfl

theorem cell22_2344161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 9].length) (baseStart_2344161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344161 prefixEnd_2344161 := by exact prefixLift 2344161
  have htrace : WordTrace (prefixWord ++ tailWord_2344161) baseStart_2344161 baseEnd_2344161 := by
    simpa [prefixWord, tailWord_2344161, baseEnd_2344161] using wordTrace_append hprefix tailTrace_2344161
  have hstable : (prefixWord ++ tailWord_2344161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344161).length < 2 ^ (prefixWord ++ tailWord_2344161).sum := by decide
  have hdescent : baseEnd_2344161 < baseStart_2344161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344165 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2344165 : Nat := 118140960795 + 2344165 * 2 ^ 59
def prefixEnd_2344165 : Nat := 4983230072969 + 3 ^ 40 * 2344165 * 2
def baseEnd_2344165 : Nat := 802455585631284118237925

theorem tailTrace_2344165 : CollatzResearch.WordTrace tailWord_2344165 prefixEnd_2344165 802455585631284118237925 := by
  unfold tailWord_2344165
  simp only [CollatzResearch.WordTrace]
  refine ⟨85498721552498031353497949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56999147701665354235665299 85498721552498031353497949)
  ·
    refine ⟨32062020582186761757561731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85498721552498031353497949 32062020582186761757561731)
    ·
      refine ⟨48093030873280142636342597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32062020582186761757561731 48093030873280142636342597)
      ·
        refine ⟨9017443288740026744314237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48093030873280142636342597 9017443288740026744314237)
        ·
          refine ⟨3381541233277510029117839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9017443288740026744314237 3381541233277510029117839)
          ·
            refine ⟨5072311849916265043676759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381541233277510029117839 5072311849916265043676759)
            ·
              refine ⟨7608467774874397565515139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072311849916265043676759 7608467774874397565515139)
              ·
                refine ⟨11412701662311596348272709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7608467774874397565515139 11412701662311596348272709)
                ·
                  refine ⟨2139881561683424315301133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11412701662311596348272709 2139881561683424315301133)
                  ·
                    refine ⟨802455585631284118237925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2139881561683424315301133 802455585631284118237925)
                    ·
                      rfl

theorem cell22_2344165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2344165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344165 prefixEnd_2344165 := by exact prefixLift 2344165
  have htrace : WordTrace (prefixWord ++ tailWord_2344165) baseStart_2344165 baseEnd_2344165 := by
    simpa [prefixWord, tailWord_2344165, baseEnd_2344165] using wordTrace_append hprefix tailTrace_2344165
  have hstable : (prefixWord ++ tailWord_2344165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344165).length < 2 ^ (prefixWord ++ tailWord_2344165).sum := by decide
  have hdescent : baseEnd_2344165 < baseStart_2344165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344236 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2344236 : Nat := 118140960795 + 2344236 * 2 ^ 59
def prefixEnd_2344236 : Nat := 4983230072969 + 3 ^ 40 * 2344236 * 2
def baseEnd_2344236 : Nat := 802479890382263599712707

theorem tailTrace_2344236 : CollatzResearch.WordTrace tailWord_2344236 prefixEnd_2344236 802479890382263599712707 := by
  unfold tailWord_2344236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42750655567620405239666281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57000874090160540319555041 42750655567620405239666281)
  ·
    refine ⟨32062991675715303929749711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42750655567620405239666281 32062991675715303929749711)
    ·
      refine ⟨48094487513572955894624567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32062991675715303929749711 48094487513572955894624567)
      ·
        refine ⟨72141731270359433841936851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48094487513572955894624567 72141731270359433841936851)
        ·
          refine ⟨108212596905539150762905277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72141731270359433841936851 108212596905539150762905277)
          ·
            refine ⟨40579723839577181536089479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108212596905539150762905277 40579723839577181536089479)
            ·
              refine ⟨60869585759365772304134219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40579723839577181536089479 60869585759365772304134219)
              ·
                refine ⟨91304378639048658456201329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60869585759365772304134219 91304378639048658456201329)
                ·
                  refine ⟨68478283979286493842150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91304378639048658456201329 68478283979286493842150997)
                  ·
                    refine ⟨802479890382263599712707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68478283979286493842150997 802479890382263599712707)
                    ·
                      rfl

theorem cell22_2344236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2344236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344236 prefixEnd_2344236 := by exact prefixLift 2344236
  have htrace : WordTrace (prefixWord ++ tailWord_2344236) baseStart_2344236 baseEnd_2344236 := by
    simpa [prefixWord, tailWord_2344236, baseEnd_2344236] using wordTrace_append hprefix tailTrace_2344236
  have hstable : (prefixWord ++ tailWord_2344236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344236).length < 2 ^ (prefixWord ++ tailWord_2344236).sum := by decide
  have hdescent : baseEnd_2344236 < baseStart_2344236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344300 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_2344300 : Nat := 118140960795 + 2344300 * 2 ^ 59
def prefixEnd_2344300 : Nat := 4983230072969 + 3 ^ 40 * 2344300 * 2
def baseEnd_2344300 : Nat := 802501798890188766112511

theorem tailTrace_2344300 : CollatzResearch.WordTrace tailWord_2344300 prefixEnd_2344300 802501798890188766112511 := by
  unfold tailWord_2344300
  simp only [CollatzResearch.WordTrace]
  refine ⟨42751822703504474704831177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57002430271339299606441569 42751822703504474704831177)
  ·
    refine ⟨32063867027628356028623383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42751822703504474704831177 32063867027628356028623383)
    ·
      refine ⟨48095800541442534042935075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32063867027628356028623383 48095800541442534042935075)
      ·
        refine ⟨72143700812163801064402613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48095800541442534042935075 72143700812163801064402613)
        ·
          refine ⟨6763471951140356349787745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72143700812163801064402613 6763471951140356349787745)
          ·
            refine ⟨5072603963355267262340809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6763471951140356349787745 5072603963355267262340809)
            ·
              refine ⟨3804452972516450446755607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5072603963355267262340809 3804452972516450446755607)
              ·
                refine ⟨5706679458774675670133411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3804452972516450446755607 5706679458774675670133411)
                ·
                  refine ⟨8560019188162013505200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5706679458774675670133411 8560019188162013505200117)
                  ·
                    refine ⟨802501798890188766112511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8560019188162013505200117 802501798890188766112511)
                    ·
                      rfl

theorem cell22_2344300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_2344300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344300 prefixEnd_2344300 := by exact prefixLift 2344300
  have htrace : WordTrace (prefixWord ++ tailWord_2344300) baseStart_2344300 baseEnd_2344300 := by
    simpa [prefixWord, tailWord_2344300, baseEnd_2344300] using wordTrace_append hprefix tailTrace_2344300
  have hstable : (prefixWord ++ tailWord_2344300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344300).length < 2 ^ (prefixWord ++ tailWord_2344300).sum := by decide
  have hdescent : baseEnd_2344300 < baseStart_2344300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344302 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_2344302 : Nat := 118140960795 + 2344302 * 2 ^ 59
def prefixEnd_2344302 : Nat := 4983230072969 + 3 ^ 40 * 2344302 * 2
def baseEnd_2344302 : Nat := 267500827843687142520835

theorem tailTrace_2344302 : CollatzResearch.WordTrace tailWord_2344302 prefixEnd_2344302 267500827843687142520835 := by
  unfold tailWord_2344302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10687964794125212968904395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57002478902001135834156773 10687964794125212968904395)
  ·
    refine ⟨16031947191187819453356593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10687964794125212968904395 16031947191187819453356593)
    ·
      refine ⟨12023960393390864590017445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16031947191187819453356593 12023960393390864590017445)
      ·
        refine ⟨2254492573760787110628271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12023960393390864590017445 2254492573760787110628271)
        ·
          refine ⟨3381738860641180665942407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254492573760787110628271 3381738860641180665942407)
          ·
            refine ⟨5072608290961770998913611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3381738860641180665942407 5072608290961770998913611)
            ·
              refine ⟨7608912436442656498370417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5072608290961770998913611 7608912436442656498370417)
              ·
                refine ⟨5706684327331992373777813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7608912436442656498370417 5706684327331992373777813)
                ·
                  refine ⟨267500827843687142520835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5706684327331992373777813 267500827843687142520835)
                  ·
                    rfl

theorem cell22_2344302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_2344302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344302 prefixEnd_2344302 := by exact prefixLift 2344302
  have htrace : WordTrace (prefixWord ++ tailWord_2344302) baseStart_2344302 baseEnd_2344302 := by
    simpa [prefixWord, tailWord_2344302, baseEnd_2344302] using wordTrace_append hprefix tailTrace_2344302
  have hstable : (prefixWord ++ tailWord_2344302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344302).length < 2 ^ (prefixWord ++ tailWord_2344302).sum := by decide
  have hdescent : baseEnd_2344302 < baseStart_2344302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344321 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2344321 : Nat := 118140960795 + 2344321 * 2 ^ 59
def prefixEnd_2344321 : Nat := 4983230072969 + 3 ^ 40 * 2344321 * 2
def baseEnd_2344321 : Nat := 802508987619351711337447

theorem tailTrace_2344321 : CollatzResearch.WordTrace tailWord_2344321 prefixEnd_2344321 802508987619351711337447 := by
  unfold tailWord_2344321
  simp only [CollatzResearch.WordTrace]
  refine ⟨85504411339932869996176817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57002940893288579997451211 85504411339932869996176817)
  ·
    refine ⟨64128308504949652497132613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85504411339932869996176817 64128308504949652497132613)
    ·
      refine ⟨12024057844678059843212365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64128308504949652497132613 12024057844678059843212365)
      ·
        refine ⟨4509021691754272441204637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12024057844678059843212365 4509021691754272441204637)
        ·
          refine ⟨1690883134407852165451739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4509021691754272441204637 1690883134407852165451739)
          ·
            refine ⟨2536324701611778248177609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690883134407852165451739 2536324701611778248177609)
            ·
              refine ⟨1902243526208833686133207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2536324701611778248177609 1902243526208833686133207)
              ·
                refine ⟨2853365289313250529199811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1902243526208833686133207 2853365289313250529199811)
                ·
                  refine ⟨4280047933969875793799717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2853365289313250529199811 4280047933969875793799717)
                  ·
                    refine ⟨802508987619351711337447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280047933969875793799717 802508987619351711337447)
                    ·
                      rfl

theorem cell22_2344321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2344321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344321 prefixEnd_2344321 := by exact prefixLift 2344321
  have htrace : WordTrace (prefixWord ++ tailWord_2344321) baseStart_2344321 baseEnd_2344321 := by
    simpa [prefixWord, tailWord_2344321, baseEnd_2344321] using wordTrace_append hprefix tailTrace_2344321
  have hstable : (prefixWord ++ tailWord_2344321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344321).length < 2 ^ (prefixWord ++ tailWord_2344321).sum := by decide
  have hdescent : baseEnd_2344321 < baseStart_2344321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344345 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 3, 3]
def baseStart_2344345 : Nat := 118140960795 + 2344345 * 2 ^ 59
def prefixEnd_2344345 : Nat := 4983230072969 + 3 ^ 40 * 2344345 * 2
def baseEnd_2344345 : Nat := 802517203309823648737373

theorem tailTrace_2344345 : CollatzResearch.WordTrace tailWord_2344345 prefixEnd_2344345 802517203309823648737373 := by
  unfold tailWord_2344345
  simp only [CollatzResearch.WordTrace]
  refine ⟨85505286691845922095050489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57003524461230614730033659 85505286691845922095050489)
  ·
    refine ⟨64128965018884441571287867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85505286691845922095050489 64128965018884441571287867)
    ·
      refine ⟨96193447528326662356931801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64128965018884441571287867 96193447528326662356931801)
      ·
        refine ⟨72145085646244996767698851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96193447528326662356931801 72145085646244996767698851)
        ·
          refine ⟨108217628469367495151548277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72145085646244996767698851 108217628469367495151548277)
          ·
            refine ⟨10145402669003202670457651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108217628469367495151548277 10145402669003202670457651)
            ·
              refine ⟨15218104003504804005686477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10145402669003202670457651 15218104003504804005686477)
              ·
                refine ⟨5706789001314301502132429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15218104003504804005686477 5706789001314301502132429)
                ·
                  refine ⟨2140045875492863063299661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5706789001314301502132429 2140045875492863063299661)
                  ·
                    refine ⟨802517203309823648737373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140045875492863063299661 802517203309823648737373)
                    ·
                      rfl

theorem cell22_2344345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_2344345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344345 prefixEnd_2344345 := by exact prefixLift 2344345
  have htrace : WordTrace (prefixWord ++ tailWord_2344345) baseStart_2344345 baseEnd_2344345 := by
    simpa [prefixWord, tailWord_2344345, baseEnd_2344345] using wordTrace_append hprefix tailTrace_2344345
  have hstable : (prefixWord ++ tailWord_2344345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344345).length < 2 ^ (prefixWord ++ tailWord_2344345).sum := by decide
  have hdescent : baseEnd_2344345 < baseStart_2344345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344396 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_2344396 : Nat := 118140960795 + 2344396 * 2 ^ 59
def prefixEnd_2344396 : Nat := 4983230072969 + 3 ^ 40 * 2344396 * 2
def baseEnd_2344396 : Nat := 802534661652076515712217

theorem tailTrace_2344396 : CollatzResearch.WordTrace tailWord_2344396 prefixEnd_2344396 802534661652076515712217 := by
  unfold tailWord_2344396
  simp only [CollatzResearch.WordTrace]
  refine ⟨42753573407330578902578521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57004764543107438536771361 42753573407330578902578521)
  ·
    refine ⟨32065180055497934176933891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42753573407330578902578521 32065180055497934176933891)
    ·
      refine ⟨48097770083246901265400837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32065180055497934176933891 48097770083246901265400837)
      ·
        refine ⟨9018331890608793987262657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48097770083246901265400837 9018331890608793987262657)
        ·
          refine ⟨6763748917956595490446993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9018331890608793987262657 6763748917956595490446993)
          ·
            refine ⟨5072811688467446617835245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6763748917956595490446993 5072811688467446617835245)
            ·
              refine ⟨1902304383175292481688217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5072811688467446617835245 1902304383175292481688217)
              ·
                refine ⟨1426728287381469361266163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902304383175292481688217 1426728287381469361266163)
                ·
                  refine ⟨2140092431072204041899245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426728287381469361266163 2140092431072204041899245)
                  ·
                    refine ⟨802534661652076515712217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140092431072204041899245 802534661652076515712217)
                    ·
                      rfl

theorem cell22_2344396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_2344396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344396 prefixEnd_2344396 := by exact prefixLift 2344396
  have htrace : WordTrace (prefixWord ++ tailWord_2344396) baseStart_2344396 baseEnd_2344396 := by
    simpa [prefixWord, tailWord_2344396, baseEnd_2344396] using wordTrace_append hprefix tailTrace_2344396
  have hstable : (prefixWord ++ tailWord_2344396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344396).length < 2 ^ (prefixWord ++ tailWord_2344396).sum := by decide
  have hdescent : baseEnd_2344396 < baseStart_2344396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344405 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2344405 : Nat := 118140960795 + 2344405 * 2 ^ 59
def prefixEnd_2344405 : Nat := 4983230072969 + 3 ^ 40 * 2344405 * 2
def baseEnd_2344405 : Nat := 802537742536003492237189

theorem tailTrace_2344405 : CollatzResearch.WordTrace tailWord_2344405 prefixEnd_2344405 802537742536003492237189 := by
  unfold tailWord_2344405
  simp only [CollatzResearch.WordTrace]
  refine ⟨85507475071628552342234669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57004983381085701561489779 85507475071628552342234669)
  ·
    refine ⟨32065303151860707128338001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85507475071628552342234669 32065303151860707128338001)
    ·
      refine ⟨24048977363895530346253501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32065303151860707128338001 24048977363895530346253501)
      ·
        refine ⟨9018366511460823879845063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24048977363895530346253501 9018366511460823879845063)
        ·
          refine ⟨13527549767191235819767595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9018366511460823879845063 13527549767191235819767595)
          ·
            refine ⟨20291324650786853729651393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13527549767191235819767595 20291324650786853729651393)
            ·
              refine ⟨15218493488090140297238545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20291324650786853729651393 15218493488090140297238545)
              ·
                refine ⟨11413870116067605222928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15218493488090140297238545 11413870116067605222928909)
                ·
                  refine ⟨4280201293525351958598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11413870116067605222928909 4280201293525351958598341)
                  ·
                    refine ⟨802537742536003492237189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280201293525351958598341 802537742536003492237189)
                    ·
                      rfl

theorem cell22_2344405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2344405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344405 prefixEnd_2344405 := by exact prefixLift 2344405
  have htrace : WordTrace (prefixWord ++ tailWord_2344405) baseStart_2344405 baseEnd_2344405 := by
    simpa [prefixWord, tailWord_2344405, baseEnd_2344405] using wordTrace_append hprefix tailTrace_2344405
  have hstable : (prefixWord ++ tailWord_2344405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344405).length < 2 ^ (prefixWord ++ tailWord_2344405).sum := by decide
  have hdescent : baseEnd_2344405 < baseStart_2344405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344435 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 4, 3]
def baseStart_2344435 : Nat := 118140960795 + 2344435 * 2 ^ 59
def prefixEnd_2344435 : Nat := 4983230072969 + 3 ^ 40 * 2344435 * 2
def baseEnd_2344435 : Nat := 802548012149093413987097

theorem tailTrace_2344435 : CollatzResearch.WordTrace tailWord_2344435 prefixEnd_2344435 802548012149093413987097 := by
  unfold tailWord_2344435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85508569261519867465826759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57005712841013244977217839 85508569261519867465826759)
  ·
    refine ⟨128262853892279801198740139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85508569261519867465826759 128262853892279801198740139)
    ·
      refine ⟨192394280838419701798110209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128262853892279801198740139 192394280838419701798110209)
      ·
        refine ⟨144295710628814776348582657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192394280838419701798110209 144295710628814776348582657)
        ·
          refine ⟨108221782971611082261436993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144295710628814776348582657 108221782971611082261436993)
          ·
            refine ⟨81166337228708311696077745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108221782971611082261436993 81166337228708311696077745)
            ·
              refine ⟨60874752921531233772058309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81166337228708311696077745 60874752921531233772058309)
              ·
                refine ⟨11414016172787106332260933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60874752921531233772058309 11414016172787106332260933)
                ·
                  refine ⟨2140128032397582437298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11414016172787106332260933 2140128032397582437298925)
                  ·
                    refine ⟨802548012149093413987097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140128032397582437298925 802548012149093413987097)
                    ·
                      rfl

theorem cell22_2344435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 3].length) (baseStart_2344435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344435 prefixEnd_2344435 := by exact prefixLift 2344435
  have htrace : WordTrace (prefixWord ++ tailWord_2344435) baseStart_2344435 baseEnd_2344435 := by
    simpa [prefixWord, tailWord_2344435, baseEnd_2344435] using wordTrace_append hprefix tailTrace_2344435
  have hstable : (prefixWord ++ tailWord_2344435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344435).length < 2 ^ (prefixWord ++ tailWord_2344435).sum := by decide
  have hdescent : baseEnd_2344435 < baseStart_2344435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344570 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_2344570 : Nat := 118140960795 + 2344570 * 2 ^ 59
def prefixEnd_2344570 : Nat := 4983230072969 + 3 ^ 40 * 2344570 * 2
def baseEnd_2344570 : Nat := 802594225407998061861683

theorem tailTrace_2344570 : CollatzResearch.WordTrace tailWord_2344570 prefixEnd_2344570 802594225407998061861683 := by
  unfold tailWord_2344570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21378373279007696380497791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57008995410687190347994109 21378373279007696380497791)
  ·
    refine ⟨32067559918511544570746687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21378373279007696380497791 32067559918511544570746687)
    ·
      refine ⟨48101339877767316856120031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32067559918511544570746687 48101339877767316856120031)
      ·
        refine ⟨72152009816650975284180047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48101339877767316856120031 72152009816650975284180047)
        ·
          refine ⟨108228014724976462926270071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72152009816650975284180047 108228014724976462926270071)
          ·
            refine ⟨162342022087464694389405107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108228014724976462926270071 162342022087464694389405107)
            ·
              refine ⟨243513033131197041584107661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162342022087464694389405107 243513033131197041584107661)
              ·
                refine ⟨91317387424198890594040373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243513033131197041584107661 91317387424198890594040373)
                ·
                  refine ⟨8561005071018645993191285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91317387424198890594040373 8561005071018645993191285)
                  ·
                    refine ⟨802594225407998061861683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8561005071018645993191285 802594225407998061861683)
                    ·
                      rfl

theorem cell22_2344570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_2344570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344570 prefixEnd_2344570 := by exact prefixLift 2344570
  have htrace : WordTrace (prefixWord ++ tailWord_2344570) baseStart_2344570 baseEnd_2344570 := by
    simpa [prefixWord, tailWord_2344570, baseEnd_2344570] using wordTrace_append hprefix tailTrace_2344570
  have hstable : (prefixWord ++ tailWord_2344570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344570).length < 2 ^ (prefixWord ++ tailWord_2344570).sum := by decide
  have hdescent : baseEnd_2344570 < baseStart_2344570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344585 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 6]
def baseStart_2344585 : Nat := 118140960795 + 2344585 * 2 ^ 59
def prefixEnd_2344585 : Nat := 4983230072969 + 3 ^ 40 * 2344585 * 2
def baseEnd_2344585 : Nat := 802599360214543022736637

theorem tailTrace_2344585 : CollatzResearch.WordTrace tailWord_2344585 prefixEnd_2344585 802599360214543022736637 := by
  unfold tailWord_2344585
  simp only [CollatzResearch.WordTrace]
  refine ⟨85514040210976443083787209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57009360140650962055858139 85514040210976443083787209)
  ·
    refine ⟨64135530158232332312840407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85514040210976443083787209 64135530158232332312840407)
    ·
      refine ⟨96203295237348498469260611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64135530158232332312840407 96203295237348498469260611)
      ·
        refine ⟨144304942856022747703890917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96203295237348498469260611 144304942856022747703890917)
        ·
          refine ⟨27057176785504265194479547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144304942856022747703890917 27057176785504265194479547)
          ·
            refine ⟨40585765178256397791719321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27057176785504265194479547 40585765178256397791719321)
            ·
              refine ⟨30439323883692298343789491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40585765178256397791719321 30439323883692298343789491)
              ·
                refine ⟨45658985825538447515684237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30439323883692298343789491 45658985825538447515684237)
                ·
                  refine ⟨17122119684576917818381589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45658985825538447515684237 17122119684576917818381589)
                  ·
                    refine ⟨802599360214543022736637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17122119684576917818381589 802599360214543022736637)
                    ·
                      rfl

theorem cell22_2344585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_2344585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344585 prefixEnd_2344585 := by exact prefixLift 2344585
  have htrace : WordTrace (prefixWord ++ tailWord_2344585) baseStart_2344585 baseEnd_2344585 := by
    simpa [prefixWord, tailWord_2344585, baseEnd_2344585] using wordTrace_append hprefix tailTrace_2344585
  have hstable : (prefixWord ++ tailWord_2344585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344585).length < 2 ^ (prefixWord ++ tailWord_2344585).sum := by decide
  have hdescent : baseEnd_2344585 < baseStart_2344585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344604 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_2344604 : Nat := 118140960795 + 2344604 * 2 ^ 59
def prefixEnd_2344604 : Nat := 4983230072969 + 3 ^ 40 * 2344604 * 2
def baseEnd_2344604 : Nat := 802605864302833306511579

theorem tailTrace_2344604 : CollatzResearch.WordTrace tailWord_2344604 prefixEnd_2344604 802605864302833306511579 := by
  unfold tailWord_2344604
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757366598953804664364433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57009822131938406219152577 42757366598953804664364433)
  ·
    refine ⟨32068024949215353498273325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42757366598953804664364433 32068024949215353498273325)
    ·
      refine ⟨12025509355955757561852497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32068024949215353498273325 12025509355955757561852497)
      ·
        refine ⟨9019132016966818171389373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12025509355955757561852497 9019132016966818171389373)
        ·
          refine ⟨3382174506362556814271015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9019132016966818171389373 3382174506362556814271015)
          ·
            refine ⟨5073261759543835221406523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382174506362556814271015 5073261759543835221406523)
            ·
              refine ⟨7609892639315752832109785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073261759543835221406523 7609892639315752832109785)
              ·
                refine ⟨5707419479486814624082339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7609892639315752832109785 5707419479486814624082339)
                ·
                  refine ⟨8561129219230221936123509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5707419479486814624082339 8561129219230221936123509)
                  ·
                    refine ⟨802605864302833306511579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8561129219230221936123509 802605864302833306511579)
                    ·
                      rfl

theorem cell22_2344604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_2344604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344604 prefixEnd_2344604 := by exact prefixLift 2344604
  have htrace : WordTrace (prefixWord ++ tailWord_2344604) baseStart_2344604 baseEnd_2344604 := by
    simpa [prefixWord, tailWord_2344604, baseEnd_2344604] using wordTrace_append hprefix tailTrace_2344604
  have hstable : (prefixWord ++ tailWord_2344604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344604).length < 2 ^ (prefixWord ++ tailWord_2344604).sum := by decide
  have hdescent : baseEnd_2344604 < baseStart_2344604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344621 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2344621 : Nat := 118140960795 + 2344621 * 2 ^ 59
def prefixEnd_2344621 : Nat := 4983230072969 + 3 ^ 40 * 2344621 * 2
def baseEnd_2344621 : Nat := 802611683750250928836527

theorem tailTrace_2344621 : CollatzResearch.WordTrace tailWord_2344621 prefixEnd_2344621 802611683750250928836527 := by
  unfold tailWord_2344621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85515353238846021232097717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57010235492564014154731811 85515353238846021232097717)
  ·
    refine ⟨8017064366141814490509161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85515353238846021232097717 8017064366141814490509161)
    ·
      refine ⟨6012798274606360867881871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8017064366141814490509161 6012798274606360867881871)
      ·
        refine ⟨9019197411909541301822807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6012798274606360867881871 9019197411909541301822807)
        ·
          refine ⟨13528796117864311952734211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9019197411909541301822807 13528796117864311952734211)
          ·
            refine ⟨20293194176796467929101317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13528796117864311952734211 20293194176796467929101317)
            ·
              refine ⟨3804973908149337736706497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20293194176796467929101317 3804973908149337736706497)
              ·
                refine ⟨2853730431112003302529873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3804973908149337736706497 2853730431112003302529873)
                ·
                  refine ⟨2140297823334002476897405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2853730431112003302529873 2140297823334002476897405)
                  ·
                    refine ⟨802611683750250928836527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140297823334002476897405 802611683750250928836527)
                    ·
                      rfl

theorem cell22_2344621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2344621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344621 prefixEnd_2344621 := by exact prefixLift 2344621
  have htrace : WordTrace (prefixWord ++ tailWord_2344621) baseStart_2344621 baseEnd_2344621 := by
    simpa [prefixWord, tailWord_2344621, baseEnd_2344621] using wordTrace_append hprefix tailTrace_2344621
  have hstable : (prefixWord ++ tailWord_2344621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344621).length < 2 ^ (prefixWord ++ tailWord_2344621).sum := by decide
  have hdescent : baseEnd_2344621 < baseStart_2344621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344632 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_2344632 : Nat := 118140960795 + 2344632 * 2 ^ 59
def prefixEnd_2344632 : Nat := 4983230072969 + 3 ^ 40 * 2344632 * 2
def baseEnd_2344632 : Nat := 802615449275050566811493

theorem tailTrace_2344632 : CollatzResearch.WordTrace tailWord_2344632 prefixEnd_2344632 802615449275050566811493 := by
  unfold tailWord_2344632
  simp only [CollatzResearch.WordTrace]
  refine ⟨42757877220903085055374075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57010502961204113407165433 42757877220903085055374075)
  ·
    refine ⟨64136815831354627583061113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42757877220903085055374075 64136815831354627583061113)
    ·
      refine ⟨48102611873515970687295835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64136815831354627583061113 48102611873515970687295835)
      ·
        refine ⟨72153917810273956030943753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48102611873515970687295835 72153917810273956030943753)
        ·
          refine ⟨54115438357705467023207815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72153917810273956030943753 54115438357705467023207815)
          ·
            refine ⟨81173157536558200534811723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54115438357705467023207815 81173157536558200534811723)
            ·
              refine ⟨121759736304837300802217585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81173157536558200534811723 121759736304837300802217585)
              ·
                refine ⟨91319802228627975601663189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121759736304837300802217585 91319802228627975601663189)
                ·
                  refine ⟨2140307864733468178163981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91319802228627975601663189 2140307864733468178163981)
                  ·
                    refine ⟨802615449275050566811493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140307864733468178163981 802615449275050566811493)
                    ·
                      rfl

theorem cell22_2344632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_2344632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344632 prefixEnd_2344632 := by exact prefixLift 2344632
  have htrace : WordTrace (prefixWord ++ tailWord_2344632) baseStart_2344632 baseEnd_2344632 := by
    simpa [prefixWord, tailWord_2344632, baseEnd_2344632] using wordTrace_append hprefix tailTrace_2344632
  have hstable : (prefixWord ++ tailWord_2344632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344632).length < 2 ^ (prefixWord ++ tailWord_2344632).sum := by decide
  have hdescent : baseEnd_2344632 < baseStart_2344632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344653 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2344653 : Nat := 118140960795 + 2344653 * 2 ^ 59
def prefixEnd_2344653 : Nat := 4983230072969 + 3 ^ 40 * 2344653 * 2
def baseEnd_2344653 : Nat := 802622638004213512036429

theorem tailTrace_2344653 : CollatzResearch.WordTrace tailWord_2344653 prefixEnd_2344653 802622638004213512036429 := by
  unfold tailWord_2344653
  simp only [CollatzResearch.WordTrace]
  refine ⟨85516520374730090697262613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57011013583153393798175075 85516520374730090697262613)
  ·
    refine ⟨4008586892565473001434185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85516520374730090697262613 4008586892565473001434185)
    ·
      refine ⟨3006440169424104751075639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008586892565473001434185 3006440169424104751075639)
      ·
        refine ⟨4509660254136157126613459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3006440169424104751075639 4509660254136157126613459)
        ·
          refine ⟨6764490381204235689920189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4509660254136157126613459 6764490381204235689920189)
          ·
            refine ⟨2536683892951588383720071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6764490381204235689920189 2536683892951588383720071)
            ·
              refine ⟨3805025839427382575580107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2536683892951588383720071 3805025839427382575580107)
              ·
                refine ⟨5707538759141073863370161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3805025839427382575580107 5707538759141073863370161)
                ·
                  refine ⟨4280654069355805397527621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5707538759141073863370161 4280654069355805397527621)
                  ·
                    refine ⟨802622638004213512036429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4280654069355805397527621 802622638004213512036429)
                    ·
                      rfl

theorem cell22_2344653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2344653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344653 prefixEnd_2344653 := by exact prefixLift 2344653
  have htrace : WordTrace (prefixWord ++ tailWord_2344653) baseStart_2344653 baseEnd_2344653 := by
    simpa [prefixWord, tailWord_2344653, baseEnd_2344653] using wordTrace_append hprefix tailTrace_2344653
  have hstable : (prefixWord ++ tailWord_2344653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344653).length < 2 ^ (prefixWord ++ tailWord_2344653).sum := by decide
  have hdescent : baseEnd_2344653 < baseStart_2344653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344666 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_2344666 : Nat := 118140960795 + 2344666 * 2 ^ 59
def prefixEnd_2344666 : Nat := 4983230072969 + 3 ^ 40 * 2344666 * 2
def baseEnd_2344666 : Nat := 802627088169885811461389

theorem tailTrace_2344666 : CollatzResearch.WordTrace tailWord_2344666 prefixEnd_2344666 802627088169885811461389 := by
  unfold tailWord_2344666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21379248630920748479371463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57011329682455329278323901 21379248630920748479371463)
  ·
    refine ⟨32068872946381122719057195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21379248630920748479371463 32068872946381122719057195)
    ·
      refine ⟨48103309419571684078585793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32068872946381122719057195 48103309419571684078585793)
      ·
        refine ⟨36077482064678763058939345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48103309419571684078585793 36077482064678763058939345)
        ·
          refine ⟨27058111548509072294204509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36077482064678763058939345 27058111548509072294204509)
          ·
            refine ⟨10146791830690902110326691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27058111548509072294204509 10146791830690902110326691)
            ·
              refine ⟨15220187746036353165490037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10146791830690902110326691 15220187746036353165490037)
              ·
                refine ⟨1426892601190908109264691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15220187746036353165490037 1426892601190908109264691)
                ·
                  refine ⟨2140338901786362163897037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426892601190908109264691 2140338901786362163897037)
                  ·
                    refine ⟨802627088169885811461389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140338901786362163897037 802627088169885811461389)
                    ·
                      rfl

theorem cell22_2344666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_2344666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344666 prefixEnd_2344666 := by exact prefixLift 2344666
  have htrace : WordTrace (prefixWord ++ tailWord_2344666) baseStart_2344666 baseEnd_2344666 := by
    simpa [prefixWord, tailWord_2344666, baseEnd_2344666] using wordTrace_append hprefix tailTrace_2344666
  have hstable : (prefixWord ++ tailWord_2344666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344666).length < 2 ^ (prefixWord ++ tailWord_2344666).sum := by decide
  have hdescent : baseEnd_2344666 < baseStart_2344666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344677 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2344677 : Nat := 118140960795 + 2344677 * 2 ^ 59
def prefixEnd_2344677 : Nat := 4983230072969 + 3 ^ 40 * 2344677 * 2
def baseEnd_2344677 : Nat := 802630853694685449436355

theorem tailTrace_2344677 : CollatzResearch.WordTrace tailWord_2344677 prefixEnd_2344677 802630853694685449436355 := by
  unfold tailWord_2344677
  simp only [CollatzResearch.WordTrace]
  refine ⟨85517395726643142796136285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57011597151095428530757523 85517395726643142796136285)
  ·
    refine ⟨32069023397491178548551107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85517395726643142796136285 32069023397491178548551107)
    ·
      refine ⟨48103535096236767822826661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32069023397491178548551107 48103535096236767822826661)
      ·
        refine ⟨9019412830544393966779999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48103535096236767822826661 9019412830544393966779999)
        ·
          refine ⟨13529119245816590950169999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9019412830544393966779999 13529119245816590950169999)
          ·
            refine ⟨20293678868724886425254999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13529119245816590950169999 20293678868724886425254999)
            ·
              refine ⟨30440518303087329637882499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20293678868724886425254999 30440518303087329637882499)
              ·
                refine ⟨45660777454630994456823749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30440518303087329637882499 45660777454630994456823749)
                ·
                  refine ⟨8561395772743311460654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45660777454630994456823749 8561395772743311460654453)
                  ·
                    refine ⟨802630853694685449436355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8561395772743311460654453 802630853694685449436355)
                    ·
                      rfl

theorem cell22_2344677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2344677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344677 prefixEnd_2344677 := by exact prefixLift 2344677
  have htrace : WordTrace (prefixWord ++ tailWord_2344677) baseStart_2344677 baseEnd_2344677 := by
    simpa [prefixWord, tailWord_2344677, baseEnd_2344677] using wordTrace_append hprefix tailTrace_2344677
  have hstable : (prefixWord ++ tailWord_2344677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344677).length < 2 ^ (prefixWord ++ tailWord_2344677).sum := by decide
  have hdescent : baseEnd_2344677 < baseStart_2344677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344694 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2344694 : Nat := 118140960795 + 2344694 * 2 ^ 59
def prefixEnd_2344694 : Nat := 4983230072969 + 3 ^ 40 * 2344694 * 2
def baseEnd_2344694 : Nat := 802636673142103071761303

theorem tailTrace_2344694 : CollatzResearch.WordTrace tailWord_2344694 prefixEnd_2344694 802636673142103071761303 := by
  unfold tailWord_2344694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5344875985473847168719071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57012010511721036466336757 5344875985473847168719071)
  ·
    refine ⟨8017313978210770753078607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5344875985473847168719071 8017313978210770753078607)
    ·
      refine ⟨12025970967316156129617911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8017313978210770753078607 12025970967316156129617911)
      ·
        refine ⟨18038956450974234194426867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12025970967316156129617911 18038956450974234194426867)
        ·
          refine ⟨27058434676461351291640301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18038956450974234194426867 27058434676461351291640301)
          ·
            refine ⟨10146913003673006734365113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27058434676461351291640301 10146913003673006734365113)
            ·
              refine ⟨7610184752754755050773835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10146913003673006734365113 7610184752754755050773835)
              ·
                refine ⟨11415277129132132576160753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610184752754755050773835 11415277129132132576160753)
                ·
                  refine ⟨8561457846849099432120565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11415277129132132576160753 8561457846849099432120565)
                  ·
                    refine ⟨802636673142103071761303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8561457846849099432120565 802636673142103071761303)
                    ·
                      rfl

theorem cell22_2344694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2344694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344694 prefixEnd_2344694 := by exact prefixLift 2344694
  have htrace : WordTrace (prefixWord ++ tailWord_2344694) baseStart_2344694 baseEnd_2344694 := by
    simpa [prefixWord, tailWord_2344694, baseEnd_2344694] using wordTrace_append hprefix tailTrace_2344694
  have hstable : (prefixWord ++ tailWord_2344694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344694).length < 2 ^ (prefixWord ++ tailWord_2344694).sum := by decide
  have hdescent : baseEnd_2344694 < baseStart_2344694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344707 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 6]
def baseStart_2344707 : Nat := 118140960795 + 2344707 * 2 ^ 59
def prefixEnd_2344707 : Nat := 4983230072969 + 3 ^ 40 * 2344707 * 2
def baseEnd_2344707 : Nat := 267547041102591790395421

theorem tailTrace_2344707 : CollatzResearch.WordTrace tailWord_2344707 prefixEnd_2344707 267547041102591790395421 := by
  unfold tailWord_2344707
  simp only [CollatzResearch.WordTrace]
  refine ⟨85518489916534457919728375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57012326611022971946485583 85518489916534457919728375)
  ·
    refine ⟨128277734874801686879592563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85518489916534457919728375 128277734874801686879592563)
    ·
      refine ⟨192416602312202530319388845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128277734874801686879592563 192416602312202530319388845)
      ·
        refine ⟨72156225867075948869770817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192416602312202530319388845 72156225867075948869770817)
        ·
          refine ⟨54117169400306961652328113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72156225867075948869770817 54117169400306961652328113)
          ·
            refine ⟨40587877050230221239246085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54117169400306961652328113 40587877050230221239246085)
            ·
              refine ⟨7610226946918166482358641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40587877050230221239246085 7610226946918166482358641)
              ·
                refine ⟨5707670210188624861768981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7610226946918166482358641 5707670210188624861768981)
                ·
                  refine ⟨267547041102591790395421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5707670210188624861768981 267547041102591790395421)
                  ·
                    rfl

theorem cell22_2344707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_2344707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344707 prefixEnd_2344707 := by exact prefixLift 2344707
  have htrace : WordTrace (prefixWord ++ tailWord_2344707) baseStart_2344707 baseEnd_2344707 := by
    simpa [prefixWord, tailWord_2344707, baseEnd_2344707] using wordTrace_append hprefix tailTrace_2344707
  have hstable : (prefixWord ++ tailWord_2344707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344707).length < 2 ^ (prefixWord ++ tailWord_2344707).sum := by decide
  have hdescent : baseEnd_2344707 < baseStart_2344707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344734 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2344734 : Nat := 118140960795 + 2344734 * 2 ^ 59
def prefixEnd_2344734 : Nat := 4983230072969 + 3 ^ 40 * 2344734 * 2
def baseEnd_2344734 : Nat := 802650365959556300761181

theorem tailTrace_2344734 : CollatzResearch.WordTrace tailWord_2344734 prefixEnd_2344734 802650365959556300761181 := by
  unfold tailWord_2344734
  simp only [CollatzResearch.WordTrace]
  refine ⟨10689934335929580191370157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57012983124957761020640837 10689934335929580191370157)
  ·
    refine ⟨4008725375973592571763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10689934335929580191370157 4008725375973592571763809)
    ·
      refine ⟨3006544031980194428822857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4008725375973592571763809 3006544031980194428822857)
      ·
        refine ⟨2254908023985145821617143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3006544031980194428822857 2254908023985145821617143)
        ·
          refine ⟨3382362035977718732425715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2254908023985145821617143 3382362035977718732425715)
          ·
            refine ⟨5073543053966578098638573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382362035977718732425715 5073543053966578098638573)
            ·
              refine ⟨1902578645237466786989465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5073543053966578098638573 1902578645237466786989465)
              ·
                refine ⟨1426933983928100090242099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1902578645237466786989465 1426933983928100090242099)
                ·
                  refine ⟨2140400975892150135363149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1426933983928100090242099 2140400975892150135363149)
                  ·
                    refine ⟨802650365959556300761181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140400975892150135363149 802650365959556300761181)
                    ·
                      rfl

theorem cell22_2344734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2344734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344734 prefixEnd_2344734 := by exact prefixLift 2344734
  have htrace : WordTrace (prefixWord ++ tailWord_2344734) baseStart_2344734 baseEnd_2344734 := by
    simpa [prefixWord, tailWord_2344734, baseEnd_2344734] using wordTrace_append hprefix tailTrace_2344734
  have hstable : (prefixWord ++ tailWord_2344734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344734).length < 2 ^ (prefixWord ++ tailWord_2344734).sum := by decide
  have hdescent : baseEnd_2344734 < baseStart_2344734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344739 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 4, 3]
def baseStart_2344739 : Nat := 118140960795 + 2344739 * 2 ^ 59
def prefixEnd_2344739 : Nat := 4983230072969 + 3 ^ 40 * 2344739 * 2
def baseEnd_2344739 : Nat := 802652077561737954386165

theorem tailTrace_2344739 : CollatzResearch.WordTrace tailWord_2344739 prefixEnd_2344739 802652077561737954386165 := by
  unfold tailWord_2344739
  simp only [CollatzResearch.WordTrace]
  refine ⟨85519657052418527384893271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57013104701612351589928847 85519657052418527384893271)
  ·
    refine ⟨128279485578627791077339907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85519657052418527384893271 128279485578627791077339907)
    ·
      refine ⟨192419228367941686616009861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128279485578627791077339907 192419228367941686616009861)
      ·
        refine ⟨36078605318989066240501849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 192419228367941686616009861 36078605318989066240501849)
        ·
          refine ⟨27058953989241799680376387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36078605318989066240501849 27058953989241799680376387)
          ·
            refine ⟨40588430983862699520564581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27058953989241799680376387 40588430983862699520564581)
            ·
              refine ⟨7610330809474256160105859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40588430983862699520564581 7610330809474256160105859)
              ·
                refine ⟨11415496214211384240158789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7610330809474256160105859 11415496214211384240158789)
                ·
                  refine ⟨2140405540164634545029773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11415496214211384240158789 2140405540164634545029773)
                  ·
                    refine ⟨802652077561737954386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140405540164634545029773 802652077561737954386165)
                    ·
                      rfl

theorem cell22_2344739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 3].length) (baseStart_2344739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344739 prefixEnd_2344739 := by exact prefixLift 2344739
  have htrace : WordTrace (prefixWord ++ tailWord_2344739) baseStart_2344739 baseEnd_2344739 := by
    simpa [prefixWord, tailWord_2344739, baseEnd_2344739] using wordTrace_append hprefix tailTrace_2344739
  have hstable : (prefixWord ++ tailWord_2344739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344739).length < 2 ^ (prefixWord ++ tailWord_2344739).sum := by decide
  have hdescent : baseEnd_2344739 < baseStart_2344739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344889 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_2344889 : Nat := 118140960795 + 2344889 * 2 ^ 59
def prefixEnd_2344889 : Nat := 4983230072969 + 3 ^ 40 * 2344889 * 2
def baseEnd_2344889 : Nat := 802703425627187563135705

theorem tailTrace_2344889 : CollatzResearch.WordTrace tailWord_2344889 prefixEnd_2344889 802703425627187563135705 := by
  unfold tailWord_2344889
  simp only [CollatzResearch.WordTrace]
  refine ⟨85525128001875103002853721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57016752001250068668569147 85525128001875103002853721)
  ·
    refine ⟨64143846001406327252140291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85525128001875103002853721 64143846001406327252140291)
    ·
      refine ⟨96215769002109490878210437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64143846001406327252140291 96215769002109490878210437)
      ·
        refine ⟨18040456687895529539664457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96215769002109490878210437 18040456687895529539664457)
        ·
          refine ⟨13530342515921647154748343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18040456687895529539664457 13530342515921647154748343)
          ·
            refine ⟨20295513773882470732122515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13530342515921647154748343 20295513773882470732122515)
            ·
              refine ⟨30443270660823706098183773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20295513773882470732122515 30443270660823706098183773)
              ·
                refine ⟨11416226497808889786818915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30443270660823706098183773 11416226497808889786818915)
                ·
                  refine ⟨17124339746713334680228373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11416226497808889786818915 17124339746713334680228373)
                  ·
                    refine ⟨802703425627187563135705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17124339746713334680228373 802703425627187563135705)
                    ·
                      rfl

theorem cell22_2344889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_2344889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344889 prefixEnd_2344889 := by exact prefixLift 2344889
  have htrace : WordTrace (prefixWord ++ tailWord_2344889) baseStart_2344889 baseEnd_2344889 := by
    simpa [prefixWord, tailWord_2344889, baseEnd_2344889] using wordTrace_append hprefix tailTrace_2344889
  have hstable : (prefixWord ++ tailWord_2344889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344889).length < 2 ^ (prefixWord ++ tailWord_2344889).sum := by decide
  have hdescent : baseEnd_2344889 < baseStart_2344889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344893 : List Nat := [1, 4, 1, 2, 3, 1, 3, 3, 4]
def baseStart_2344893 : Nat := 118140960795 + 2344893 * 2 ^ 59
def prefixEnd_2344893 : Nat := 4983230072969 + 3 ^ 40 * 2344893 * 2
def baseEnd_2344893 : Nat := 267568264969644295345231

theorem tailTrace_2344893 : CollatzResearch.WordTrace tailWord_2344893 prefixEnd_2344893 267568264969644295345231 := by
  unfold tailWord_2344893
  simp only [CollatzResearch.WordTrace]
  refine ⟨85525273893860611685999333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57016849262573741123999555 85525273893860611685999333)
  ·
    refine ⟨16035988855098864691124875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85525273893860611685999333 16035988855098864691124875)
    ·
      refine ⟨24053983282648297036687313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16035988855098864691124875 24053983282648297036687313)
      ·
        refine ⟨18040487461986222777515485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24053983282648297036687313 18040487461986222777515485)
        ·
          refine ⟨6765182798244833541568307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18040487461986222777515485 6765182798244833541568307)
          ·
            refine ⟨10147774197367250312352461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765182798244833541568307 10147774197367250312352461)
            ·
              refine ⟨3805415324012718867132173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10147774197367250312352461 3805415324012718867132173)
              ·
                refine ⟨1427030746504769575174565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3805415324012718867132173 1427030746504769575174565)
                ·
                  refine ⟨267568264969644295345231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427030746504769575174565 267568264969644295345231)
                  ·
                    rfl

theorem cell22_2344893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_2344893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344893 prefixEnd_2344893 := by exact prefixLift 2344893
  have htrace : WordTrace (prefixWord ++ tailWord_2344893) baseStart_2344893 baseEnd_2344893 := by
    simpa [prefixWord, tailWord_2344893, baseEnd_2344893] using wordTrace_append hprefix tailTrace_2344893
  have hstable : (prefixWord ++ tailWord_2344893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344893).length < 2 ^ (prefixWord ++ tailWord_2344893).sum := by decide
  have hdescent : baseEnd_2344893 < baseStart_2344893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344904 : List Nat := [2, 1, 3, 1, 4, 1, 10]
def baseStart_2344904 : Nat := 118140960795 + 2344904 * 2 ^ 59
def prefixEnd_2344904 : Nat := 4983230072969 + 3 ^ 40 * 2344904 * 2
def baseEnd_2344904 : Nat := 29729946682730834222617

theorem tailTrace_2344904 : CollatzResearch.WordTrace tailWord_2344904 prefixEnd_2344904 29729946682730834222617 := by
  unfold tailWord_2344904
  simp only [CollatzResearch.WordTrace]
  refine ⟨42762837548410380282324883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57017116731213840376433177 42762837548410380282324883)
  ·
    refine ⟨64144256322615570423487325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42762837548410380282324883 64144256322615570423487325)
    ·
      refine ⟨24054096120980838908807747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64144256322615570423487325 24054096120980838908807747)
      ·
        refine ⟨36081144181471258363211621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24054096120980838908807747 36081144181471258363211621)
        ·
          refine ⟨6765214534025860943102179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36081144181471258363211621 6765214534025860943102179)
          ·
            refine ⟨10147821801038791414653269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6765214534025860943102179 10147821801038791414653269)
            ·
              refine ⟨29729946682730834222617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10147821801038791414653269 29729946682730834222617)
              ·
                rfl

theorem cell22_2344904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 10].length) (baseStart_2344904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344904 prefixEnd_2344904 := by exact prefixLift 2344904
  have htrace : WordTrace (prefixWord ++ tailWord_2344904) baseStart_2344904 baseEnd_2344904 := by
    simpa [prefixWord, tailWord_2344904, baseEnd_2344904] using wordTrace_append hprefix tailTrace_2344904
  have hstable : (prefixWord ++ tailWord_2344904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344904).length < 2 ^ (prefixWord ++ tailWord_2344904).sum := by decide
  have hdescent : baseEnd_2344904 < baseStart_2344904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344921 : List Nat := [1, 2, 1, 2, 6, 1, 2, 7]
def baseStart_2344921 : Nat := 118140960795 + 2344921 * 2 ^ 59
def prefixEnd_2344921 : Nat := 4983230072969 + 3 ^ 40 * 2344921 * 2
def baseEnd_2344921 : Nat := 89190486653461127370623

theorem tailTrace_2344921 : CollatzResearch.WordTrace tailWord_2344921 prefixEnd_2344921 89190486653461127370623 := by
  unfold tailWord_2344921
  simp only [CollatzResearch.WordTrace]
  refine ⟨85526295137759172468018617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57017530091839448312012411 85526295137759172468018617)
  ·
    refine ⟨64144721353319379351013963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85526295137759172468018617 64144721353319379351013963)
    ·
      refine ⟨96217082029979069026520945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64144721353319379351013963 96217082029979069026520945)
      ·
        refine ⟨72162811522484301769890709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96217082029979069026520945 72162811522484301769890709)
        ·
          refine ⟨3382631790116451645463627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72162811522484301769890709 3382631790116451645463627)
          ·
            refine ⟨5073947685174677468195441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382631790116451645463627 5073947685174677468195441)
            ·
              refine ⟨3805460763881008101146581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5073947685174677468195441 3805460763881008101146581)
              ·
                refine ⟨89190486653461127370623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3805460763881008101146581 89190486653461127370623)
                ·
                  rfl

theorem cell22_2344921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 7].length) (baseStart_2344921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344921 prefixEnd_2344921 := by exact prefixLift 2344921
  have htrace : WordTrace (prefixWord ++ tailWord_2344921) baseStart_2344921 baseEnd_2344921 := by
    simpa [prefixWord, tailWord_2344921, baseEnd_2344921] using wordTrace_append hprefix tailTrace_2344921
  have hstable : (prefixWord ++ tailWord_2344921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344921).length < 2 ^ (prefixWord ++ tailWord_2344921).sum := by decide
  have hdescent : baseEnd_2344921 < baseStart_2344921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344925 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2344925 : Nat := 118140960795 + 2344925 * 2 ^ 59
def prefixEnd_2344925 : Nat := 4983230072969 + 3 ^ 40 * 2344925 * 2
def baseEnd_2344925 : Nat := 802715749162895469235595

theorem tailTrace_2344925 : CollatzResearch.WordTrace tailWord_2344925 prefixEnd_2344925 802715749162895469235595 := by
  unfold tailWord_2344925
  simp only [CollatzResearch.WordTrace]
  refine ⟨85526441029744681151164229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57017627353163120767442819 85526441029744681151164229)
  ·
    refine ⟨16036207693077127715843293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85526441029744681151164229 16036207693077127715843293)
    ·
      refine ⟨6013577884903922893441235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16036207693077127715843293 6013577884903922893441235)
      ·
        refine ⟨9020366827355884340161853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6013577884903922893441235 9020366827355884340161853)
        ·
          refine ⟨3382637560258456627560695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9020366827355884340161853 3382637560258456627560695)
          ·
            refine ⟨5073956340387684941341043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382637560258456627560695 5073956340387684941341043)
            ·
              refine ⟨7610934510581527412011565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5073956340387684941341043 7610934510581527412011565)
              ·
                refine ⟨2854100441468072779504337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7610934510581527412011565 2854100441468072779504337)
                ·
                  refine ⟨2140575331101054584628253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854100441468072779504337 2140575331101054584628253)
                  ·
                    refine ⟨802715749162895469235595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140575331101054584628253 802715749162895469235595)
                    ·
                      rfl

theorem cell22_2344925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2344925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344925 prefixEnd_2344925 := by exact prefixLift 2344925
  have htrace : WordTrace (prefixWord ++ tailWord_2344925) baseStart_2344925 baseEnd_2344925 := by
    simpa [prefixWord, tailWord_2344925, baseEnd_2344925] using wordTrace_append hprefix tailTrace_2344925
  have hstable : (prefixWord ++ tailWord_2344925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344925).length < 2 ^ (prefixWord ++ tailWord_2344925).sum := by decide
  have hdescent : baseEnd_2344925 < baseStart_2344925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2344936 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2344936 : Nat := 118140960795 + 2344936 * 2 ^ 59
def prefixEnd_2344936 : Nat := 4983230072969 + 3 ^ 40 * 2344936 * 2
def baseEnd_2344936 : Nat := 802719514687695107210561

theorem tailTrace_2344936 : CollatzResearch.WordTrace tailWord_2344936 prefixEnd_2344936 802719514687695107210561 := by
  unfold tailWord_2344936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42763421116352415014907331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57017894821803220019876441 42763421116352415014907331)
  ·
    refine ⟨64145131674528622522360997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42763421116352415014907331 64145131674528622522360997)
    ·
      refine ⟨12027212188974116722942687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64145131674528622522360997 12027212188974116722942687)
      ·
        refine ⟨18040818283461175084414031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12027212188974116722942687 18040818283461175084414031)
        ·
          refine ⟨27061227425191762626621047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18040818283461175084414031 27061227425191762626621047)
          ·
            refine ⟨40591841137787643939931571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27061227425191762626621047 40591841137787643939931571)
            ·
              refine ⟨60887761706681465909897357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40591841137787643939931571 60887761706681465909897357)
              ·
                refine ⟨22832910640005549716211509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60887761706681465909897357 22832910640005549716211509)
                ·
                  refine ⟨2140585372500520285894829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22832910640005549716211509 2140585372500520285894829)
                  ·
                    refine ⟨802719514687695107210561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140585372500520285894829 802719514687695107210561)
                    ·
                      rfl

theorem cell22_2344936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2344936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2344936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2344936 prefixEnd_2344936 := by exact prefixLift 2344936
  have htrace : WordTrace (prefixWord ++ tailWord_2344936) baseStart_2344936 baseEnd_2344936 := by
    simpa [prefixWord, tailWord_2344936, baseEnd_2344936] using wordTrace_append hprefix tailTrace_2344936
  have hstable : (prefixWord ++ tailWord_2344936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2344936).length < 2 ^ (prefixWord ++ tailWord_2344936).sum := by decide
  have hdescent : baseEnd_2344936 < baseStart_2344936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2344936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345056 : List Nat := [2, 1, 1, 3, 2, 4, 1, 8]
def baseStart_2345056 : Nat := 118140960795 + 2345056 * 2 ^ 59
def prefixEnd_2345056 : Nat := 4983230072969 + 3 ^ 40 * 2345056 * 2
def baseEnd_2345056 : Nat := 89195621460006088245577

theorem tailTrace_2345056 : CollatzResearch.WordTrace tailWord_2345056 prefixEnd_2345056 89195621460006088245577 := by
  unfold tailWord_2345056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42765609496135045262091511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57020812661513393682788681 42765609496135045262091511)
  ·
    refine ⟨64148414244202567893137267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42765609496135045262091511 64148414244202567893137267)
    ·
      refine ⟨96222621366303851839705901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64148414244202567893137267 96222621366303851839705901)
      ·
        refine ⟨36083483012363944439889713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96222621366303851839705901 36083483012363944439889713)
        ·
          refine ⟨27062612259272958329917285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36083483012363944439889713 27062612259272958329917285)
          ·
            refine ⟨5074239798613679686859491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27062612259272958329917285 5074239798613679686859491)
            ·
              refine ⟨7611359697920519530289237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074239798613679686859491 7611359697920519530289237)
              ·
                refine ⟨89195621460006088245577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7611359697920519530289237 89195621460006088245577)
                ·
                  rfl

theorem cell22_2345056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_2345056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345056 prefixEnd_2345056 := by exact prefixLift 2345056
  have htrace : WordTrace (prefixWord ++ tailWord_2345056) baseStart_2345056 baseEnd_2345056 := by
    simpa [prefixWord, tailWord_2345056, baseEnd_2345056] using wordTrace_append hprefix tailTrace_2345056
  have hstable : (prefixWord ++ tailWord_2345056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345056).length < 2 ^ (prefixWord ++ tailWord_2345056).sum := by decide
  have hdescent : baseEnd_2345056 < baseStart_2345056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345150 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2345150 : Nat := 118140960795 + 2345150 * 2 ^ 59
def prefixEnd_2345150 : Nat := 4983230072969 + 3 ^ 40 * 2345150 * 2
def baseEnd_2345150 : Nat := 802792771261069882359905

theorem tailTrace_2345150 : CollatzResearch.WordTrace tailWord_2345150 prefixEnd_2345150 802792771261069882359905 := by
  unfold tailWord_2345150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691830931741193072263113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57023098302619696385403269 10691830931741193072263113)
  ·
    refine ⟨8018873198805894804197335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10691830931741193072263113 8018873198805894804197335)
    ·
      refine ⟨12028309798208842206296003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8018873198805894804197335 12028309798208842206296003)
      ·
        refine ⟨18042464697313263309444005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12028309798208842206296003 18042464697313263309444005)
        ·
          refine ⟨3382962130746236870520751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18042464697313263309444005 3382962130746236870520751)
          ·
            refine ⟨5074443196119355305781127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3382962130746236870520751 5074443196119355305781127)
            ·
              refine ⟨7611664794179032958671691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074443196119355305781127 7611664794179032958671691)
              ·
                refine ⟨11417497191268549438007537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7611664794179032958671691 11417497191268549438007537)
                ·
                  refine ⟨8563122893451412078505653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11417497191268549438007537 8563122893451412078505653)
                  ·
                    refine ⟨802792771261069882359905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8563122893451412078505653 802792771261069882359905)
                    ·
                      rfl

theorem cell22_2345150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2345150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345150 prefixEnd_2345150 := by exact prefixLift 2345150
  have htrace : WordTrace (prefixWord ++ tailWord_2345150) baseStart_2345150 baseEnd_2345150 := by
    simpa [prefixWord, tailWord_2345150, baseEnd_2345150] using wordTrace_append hprefix tailTrace_2345150
  have hstable : (prefixWord ++ tailWord_2345150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345150).length < 2 ^ (prefixWord ++ tailWord_2345150).sum := by decide
  have hdescent : baseEnd_2345150 < baseStart_2345150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345178 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_2345178 : Nat := 118140960795 + 2345178 * 2 ^ 59
def prefixEnd_2345178 : Nat := 4983230072969 + 3 ^ 40 * 2345178 * 2
def baseEnd_2345178 : Nat := 802802356233287142659819

theorem tailTrace_2345178 : CollatzResearch.WordTrace tailWord_2345178 prefixEnd_2345178 802802356233287142659819 := by
  unfold tailWord_2345178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383917174457026340031047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57023779131885403573416125 21383917174457026340031047)
  ·
    refine ⟨32075875761685539510046571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21383917174457026340031047 32075875761685539510046571)
    ·
      refine ⟨48113813642528309265069857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32075875761685539510046571 48113813642528309265069857)
      ·
        refine ⟨36085360231896231948802393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48113813642528309265069857 36085360231896231948802393)
        ·
          refine ⟨27064020173922173961601795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36085360231896231948802393 27064020173922173961601795)
          ·
            refine ⟨40596030260883260942402693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27064020173922173961601795 40596030260883260942402693)
            ·
              refine ⟨7611755673915611426700505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40596030260883260942402693 7611755673915611426700505)
              ·
                refine ⟨5708816755436708570025379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7611755673915611426700505 5708816755436708570025379)
                ·
                  refine ⟨8563225133155062855038069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5708816755436708570025379 8563225133155062855038069)
                  ·
                    refine ⟨802802356233287142659819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8563225133155062855038069 802802356233287142659819)
                    ·
                      rfl

theorem cell22_2345178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_2345178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345178 prefixEnd_2345178 := by exact prefixLift 2345178
  have htrace : WordTrace (prefixWord ++ tailWord_2345178) baseStart_2345178 baseEnd_2345178 := by
    simpa [prefixWord, tailWord_2345178, baseEnd_2345178] using wordTrace_append hprefix tailTrace_2345178
  have hstable : (prefixWord ++ tailWord_2345178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345178).length < 2 ^ (prefixWord ++ tailWord_2345178).sum := by decide
  have hdescent : baseEnd_2345178 < baseStart_2345178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345186 : List Nat := [3, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2345186 : Nat := 118140960795 + 2345186 * 2 ^ 59
def prefixEnd_2345186 : Nat := 4983230072969 + 3 ^ 40 * 2345186 * 2
def baseEnd_2345186 : Nat := 267601698265592596153265

theorem tailTrace_2345186 : CollatzResearch.WordTrace tailWord_2345186 prefixEnd_2345186 267601698265592596153265 := by
  unfold tailWord_2345186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21383990120449780681603853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57023973654532748484276941 21383990120449780681603853)
  ·
    refine ⟨8018996295168667755601445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21383990120449780681603853 8018996295168667755601445)
    ·
      refine ⟨1503561805344125204175271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8018996295168667755601445 1503561805344125204175271)
      ·
        refine ⟨2255342708016187806262907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503561805344125204175271 2255342708016187806262907)
        ·
          refine ⟨3383014062024281709394361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2255342708016187806262907 3383014062024281709394361)
          ·
            refine ⟨2537260546518211282045771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383014062024281709394361 2537260546518211282045771)
            ·
              refine ⟨3805890819777316923068657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537260546518211282045771 3805890819777316923068657)
              ·
                refine ⟨2854418114832987692301493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3805890819777316923068657 2854418114832987692301493)
                ·
                  refine ⟨267601698265592596153265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854418114832987692301493 267601698265592596153265)
                  ·
                    rfl

theorem cell22_2345186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2345186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345186 prefixEnd_2345186 := by exact prefixLift 2345186
  have htrace : WordTrace (prefixWord ++ tailWord_2345186) baseStart_2345186 baseEnd_2345186 := by
    simpa [prefixWord, tailWord_2345186, baseEnd_2345186] using wordTrace_append hprefix tailTrace_2345186
  have hstable : (prefixWord ++ tailWord_2345186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345186).length < 2 ^ (prefixWord ++ tailWord_2345186).sum := by decide
  have hdescent : baseEnd_2345186 < baseStart_2345186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345225 : List Nat := [1, 2, 1, 1, 3, 6, 2, 6]
def baseStart_2345225 : Nat := 118140960795 + 2345225 * 2 ^ 59
def prefixEnd_2345225 : Nat := 4983230072969 + 3 ^ 40 * 2345225 * 2
def baseEnd_2345225 : Nat := 89202049477088298526075

theorem tailTrace_2345225 : CollatzResearch.WordTrace tailWord_2345225 prefixEnd_2345225 89202049477088298526075 := by
  unfold tailWord_2345225
  simp only [CollatzResearch.WordTrace]
  refine ⟨85537382928657832387085129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57024921952438554924723419 85537382928657832387085129)
  ·
    refine ⟨64153037196493374290313847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85537382928657832387085129 64153037196493374290313847)
    ·
      refine ⟨96229555794740061435470771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64153037196493374290313847 96229555794740061435470771)
      ·
        refine ⟨144344333692110092153206157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96229555794740061435470771 144344333692110092153206157)
        ·
          refine ⟨54129125134541284557452309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144344333692110092153206157 54129125134541284557452309)
          ·
            refine ⟨2537302740681622713630577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54129125134541284557452309 2537302740681622713630577)
            ·
              refine ⟨1902977055511217035222933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537302740681622713630577 1902977055511217035222933)
              ·
                refine ⟨89202049477088298526075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1902977055511217035222933 89202049477088298526075)
                ·
                  rfl

theorem cell22_2345225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 6].length) (baseStart_2345225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345225 prefixEnd_2345225 := by exact prefixLift 2345225
  have htrace : WordTrace (prefixWord ++ tailWord_2345225) baseStart_2345225 baseEnd_2345225 := by
    simpa [prefixWord, tailWord_2345225, baseEnd_2345225] using wordTrace_append hprefix tailTrace_2345225
  have hstable : (prefixWord ++ tailWord_2345225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345225).length < 2 ^ (prefixWord ++ tailWord_2345225).sum := by decide
  have hdescent : baseEnd_2345225 < baseStart_2345225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345330 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2345330 : Nat := 118140960795 + 2345330 * 2 ^ 59
def prefixEnd_2345330 : Nat := 4983230072969 + 3 ^ 40 * 2345330 * 2
def baseEnd_2345330 : Nat := 802854388939609412859353

theorem tailTrace_2345330 : CollatzResearch.WordTrace tailWord_2345330 prefixEnd_2345330 802854388939609412859353 := by
  unfold tailWord_2345330
  simp only [CollatzResearch.WordTrace]
  refine ⟨21385303148319358829914361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57027475062184956879771629 21385303148319358829914361)
  ·
    refine ⟨16038977361239519122435771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21385303148319358829914361 16038977361239519122435771)
    ·
      refine ⟨24058466041859278683653657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16038977361239519122435771 24058466041859278683653657)
      ·
        refine ⟨18043849531394459012740243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24058466041859278683653657 18043849531394459012740243)
        ·
          refine ⟨27065774297091688519110365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18043849531394459012740243 27065774297091688519110365)
          ·
            refine ⟨10149665361409383194666387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27065774297091688519110365 10149665361409383194666387)
            ·
              refine ⟨15224498042114074791999581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10149665361409383194666387 15224498042114074791999581)
              ·
                refine ⟨5709186765792778046999843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15224498042114074791999581 5709186765792778046999843)
                ·
                  refine ⟨8563780148689167070499765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5709186765792778046999843 8563780148689167070499765)
                  ·
                    refine ⟨802854388939609412859353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8563780148689167070499765 802854388939609412859353)
                    ·
                      rfl

theorem cell22_2345330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2345330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345330 prefixEnd_2345330 := by exact prefixLift 2345330
  have htrace : WordTrace (prefixWord ++ tailWord_2345330) baseStart_2345330 baseEnd_2345330 := by
    simpa [prefixWord, tailWord_2345330, baseEnd_2345330] using wordTrace_append hprefix tailTrace_2345330
  have hstable : (prefixWord ++ tailWord_2345330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345330).length < 2 ^ (prefixWord ++ tailWord_2345330).sum := by decide
  have hdescent : baseEnd_2345330 < baseStart_2345330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345364 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2345364 : Nat := 118140960795 + 2345364 * 2 ^ 59
def prefixEnd_2345364 : Nat := 4983230072969 + 3 ^ 40 * 2345364 * 2
def baseEnd_2345364 : Nat := 802866027834444657509249

theorem tailTrace_2345364 : CollatzResearch.WordTrace tailWord_2345364 prefixEnd_2345364 802866027834444657509249 := by
  unfold tailWord_2345364
  simp only [CollatzResearch.WordTrace]
  refine ⟨42771226337577129563197573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57028301783436172750930097 42771226337577129563197573)
  ·
    refine ⟨8019604938295711793099545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42771226337577129563197573 8019604938295711793099545)
    ·
      refine ⟨6014703703721783844824659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019604938295711793099545 6014703703721783844824659)
      ·
        refine ⟨9022055555582675767236989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014703703721783844824659 9022055555582675767236989)
        ·
          refine ⟨3383270833343503412713871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9022055555582675767236989 3383270833343503412713871)
          ·
            refine ⟨5074906250015255119070807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383270833343503412713871 5074906250015255119070807)
            ·
              refine ⟨7612359375022882678606211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5074906250015255119070807 7612359375022882678606211)
              ·
                refine ⟨11418539062534324017909317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7612359375022882678606211 11418539062534324017909317)
                ·
                  refine ⟨2140976074225185753357997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11418539062534324017909317 2140976074225185753357997)
                  ·
                    refine ⟨802866027834444657509249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2140976074225185753357997 802866027834444657509249)
                    ·
                      rfl

theorem cell22_2345364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2345364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345364 prefixEnd_2345364 := by exact prefixLift 2345364
  have htrace : WordTrace (prefixWord ++ tailWord_2345364) baseStart_2345364 baseEnd_2345364 := by
    simpa [prefixWord, tailWord_2345364, baseEnd_2345364] using wordTrace_append hprefix tailTrace_2345364
  have hstable : (prefixWord ++ tailWord_2345364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345364).length < 2 ^ (prefixWord ++ tailWord_2345364).sum := by decide
  have hdescent : baseEnd_2345364 < baseStart_2345364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345405 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2345405 : Nat := 118140960795 + 2345405 * 2 ^ 59
def prefixEnd_2345405 : Nat := 4983230072969 + 3 ^ 40 * 2345405 * 2
def baseEnd_2345405 : Nat := 267626687657444739078041

theorem tailTrace_2345405 : CollatzResearch.WordTrace tailWord_2345405 prefixEnd_2345405 267626687657444739078041 := by
  unfold tailWord_2345405
  simp only [CollatzResearch.WordTrace]
  refine ⟨85543948068005723128637669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57029298712003815419091779 85543948068005723128637669)
  ·
    refine ⟨16039490262751073086619563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85543948068005723128637669 16039490262751073086619563)
    ·
      refine ⟨24059235394126609629929345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16039490262751073086619563 24059235394126609629929345)
      ·
        refine ⟨18044426545594957222447009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24059235394126609629929345 18044426545594957222447009)
        ·
          refine ⟨13533319909196217916835257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18044426545594957222447009 13533319909196217916835257)
          ·
            refine ⟨10149989931897163437626443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13533319909196217916835257 10149989931897163437626443)
            ·
              refine ⟨15224984897845745156439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10149989931897163437626443 15224984897845745156439665)
              ·
                refine ⟨11418738673384308867329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15224984897845745156439665 11418738673384308867329749)
                ·
                  refine ⟨267626687657444739078041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11418738673384308867329749 267626687657444739078041)
                  ·
                    rfl

theorem cell22_2345405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2345405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345405 prefixEnd_2345405 := by exact prefixLift 2345405
  have htrace : WordTrace (prefixWord ++ tailWord_2345405) baseStart_2345405 baseEnd_2345405 := by
    simpa [prefixWord, tailWord_2345405, baseEnd_2345405] using wordTrace_append hprefix tailTrace_2345405
  have hstable : (prefixWord ++ tailWord_2345405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345405).length < 2 ^ (prefixWord ++ tailWord_2345405).sum := by decide
  have hdescent : baseEnd_2345405 < baseStart_2345405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345439 : List Nat := [1, 1, 2, 3, 3, 4, 2, 1, 5]
def baseStart_2345439 : Nat := 118140960795 + 2345439 * 2 ^ 59
def prefixEnd_2345439 : Nat := 4983230072969 + 3 ^ 40 * 2345439 * 2
def baseEnd_2345439 : Nat := 267630567289056487294673

theorem tailTrace_2345439 : CollatzResearch.WordTrace tailWord_2345439 prefixEnd_2345439 267630567289056487294673 := by
  unfold tailWord_2345439
  simp only [CollatzResearch.WordTrace]
  refine ⟨85545188149882546935375371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57030125433255031290250247 85545188149882546935375371)
  ·
    refine ⟨128317782224823820403063057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85545188149882546935375371 128317782224823820403063057)
    ·
      refine ⟨96238336668617865302297293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128317782224823820403063057 96238336668617865302297293)
      ·
        refine ⟨36089376250731699488361485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96238336668617865302297293 36089376250731699488361485)
        ·
          refine ⟨13533516094024387308135557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36089376250731699488361485 13533516094024387308135557)
          ·
            refine ⟨2537534267629572620275417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13533516094024387308135557 2537534267629572620275417)
            ·
              refine ⟨1903150700722179465206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2537534267629572620275417 1903150700722179465206563)
              ·
                refine ⟨2854726051083269197809845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903150700722179465206563 2854726051083269197809845)
                ·
                  refine ⟨267630567289056487294673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854726051083269197809845 267630567289056487294673)
                  ·
                    rfl

theorem cell22_2345439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 5].length) (baseStart_2345439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345439 prefixEnd_2345439 := by exact prefixLift 2345439
  have htrace : WordTrace (prefixWord ++ tailWord_2345439) baseStart_2345439 baseEnd_2345439 := by
    simpa [prefixWord, tailWord_2345439, baseEnd_2345439] using wordTrace_append hprefix tailTrace_2345439
  have hstable : (prefixWord ++ tailWord_2345439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345439).length < 2 ^ (prefixWord ++ tailWord_2345439).sum := by decide
  have hdescent : baseEnd_2345439 < baseStart_2345439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345465 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_2345465 : Nat := 118140960795 + 2345465 * 2 ^ 59
def prefixEnd_2345465 : Nat := 4983230072969 + 3 ^ 40 * 2345465 * 2
def baseEnd_2345465 : Nat := 802900602198514060733939

theorem tailTrace_2345465 : CollatzResearch.WordTrace tailWord_2345465 prefixEnd_2345465 802900602198514060733939 := by
  unfold tailWord_2345465
  simp only [CollatzResearch.WordTrace]
  refine ⟨85546136447788353375821849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57030757631858902250547899 85546136447788353375821849)
  ·
    refine ⟨64159602335841265031866387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85546136447788353375821849 64159602335841265031866387)
    ·
      refine ⟨96239403503761897547799581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64159602335841265031866387 96239403503761897547799581)
      ·
        refine ⟨36089776313910711580424843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96239403503761897547799581 36089776313910711580424843)
        ·
          refine ⟨54134664470866067370637265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36089776313910711580424843 54134664470866067370637265)
          ·
            refine ⟨40600998353149550527977949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54134664470866067370637265 40600998353149550527977949)
            ·
              refine ⟨15225374382431081447991731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40600998353149550527977949 15225374382431081447991731)
              ·
                refine ⟨22838061573646622171987597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15225374382431081447991731 22838061573646622171987597)
                ·
                  refine ⟨8564273090117483314495349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22838061573646622171987597 8564273090117483314495349)
                  ·
                    refine ⟨802900602198514060733939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8564273090117483314495349 802900602198514060733939)
                    ·
                      rfl

theorem cell22_2345465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_2345465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345465 prefixEnd_2345465 := by exact prefixLift 2345465
  have htrace : WordTrace (prefixWord ++ tailWord_2345465) baseStart_2345465 baseEnd_2345465 := by
    simpa [prefixWord, tailWord_2345465, baseEnd_2345465] using wordTrace_append hprefix tailTrace_2345465
  have hstable : (prefixWord ++ tailWord_2345465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345465).length < 2 ^ (prefixWord ++ tailWord_2345465).sum := by decide
  have hdescent : baseEnd_2345465 < baseStart_2345465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345469 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_2345469 : Nat := 118140960795 + 2345469 * 2 ^ 59
def prefixEnd_2345469 : Nat := 4983230072969 + 3 ^ 40 * 2345469 * 2
def baseEnd_2345469 : Nat := 802901971480259383633927

theorem tailTrace_2345469 : CollatzResearch.WordTrace tailWord_2345469 prefixEnd_2345469 802901971480259383633927 := by
  unfold tailWord_2345469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85546282339773862058967461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57030854893182574705978307 85546282339773862058967461)
  ·
    refine ⟨16039927938707599136056399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85546282339773862058967461 16039927938707599136056399)
    ·
      refine ⟨24059891908061398704084599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16039927938707599136056399 24059891908061398704084599)
      ·
        refine ⟨36089837862092098056126899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24059891908061398704084599 36089837862092098056126899)
        ·
          refine ⟨54134756793138147084190349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36089837862092098056126899 54134756793138147084190349)
          ·
            refine ⟨20300533797426805156571381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54134756793138147084190349 20300533797426805156571381)
            ·
              refine ⟨1903175043508762983428567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20300533797426805156571381 1903175043508762983428567)
              ·
                refine ⟨2854762565263144475142851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903175043508762983428567 2854762565263144475142851)
                ·
                  refine ⟨4282143847894716712714277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2854762565263144475142851 4282143847894716712714277)
                  ·
                    refine ⟨802901971480259383633927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282143847894716712714277 802901971480259383633927)
                    ·
                      rfl

theorem cell22_2345469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_2345469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345469 prefixEnd_2345469 := by exact prefixLift 2345469
  have htrace : WordTrace (prefixWord ++ tailWord_2345469) baseStart_2345469 baseEnd_2345469 := by
    simpa [prefixWord, tailWord_2345469, baseEnd_2345469] using wordTrace_append hprefix tailTrace_2345469
  have hstable : (prefixWord ++ tailWord_2345469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345469).length < 2 ^ (prefixWord ++ tailWord_2345469).sum := by decide
  have hdescent : baseEnd_2345469 < baseStart_2345469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345480 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2345480 : Nat := 118140960795 + 2345480 * 2 ^ 59
def prefixEnd_2345480 : Nat := 4983230072969 + 3 ^ 40 * 2345480 * 2
def baseEnd_2345480 : Nat := 802905737005059021608893

theorem tailTrace_2345480 : CollatzResearch.WordTrace tailWord_2345480 prefixEnd_2345480 802905737005059021608893 := by
  unfold tailWord_2345480
  simp only [CollatzResearch.WordTrace]
  refine ⟨42773341771367005468808947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57031122361822673958411929 42773341771367005468808947)
  ·
    refine ⟨64160012657050508203213421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42773341771367005468808947 64160012657050508203213421)
    ·
      refine ⟨24060004746393940576205033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64160012657050508203213421 24060004746393940576205033)
      ·
        refine ⟨18045003559795455432153775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24060004746393940576205033 18045003559795455432153775)
        ·
          refine ⟨27067505339693183148230663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18045003559795455432153775 27067505339693183148230663)
          ·
            refine ⟨40601258009539774722345995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27067505339693183148230663 40601258009539774722345995)
            ·
              refine ⟨60901887014309662083518993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40601258009539774722345995 60901887014309662083518993)
              ·
                refine ⟨45676415260732246562639245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60901887014309662083518993 45676415260732246562639245)
                ·
                  refine ⟨17128655722774592460989717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45676415260732246562639245 17128655722774592460989717)
                  ·
                    refine ⟨802905737005059021608893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17128655722774592460989717 802905737005059021608893)
                    ·
                      rfl

theorem cell22_2345480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2345480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345480 prefixEnd_2345480 := by exact prefixLift 2345480
  have htrace : WordTrace (prefixWord ++ tailWord_2345480) baseStart_2345480 baseEnd_2345480 := by
    simpa [prefixWord, tailWord_2345480, baseEnd_2345480] using wordTrace_append hprefix tailTrace_2345480
  have hstable : (prefixWord ++ tailWord_2345480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345480).length < 2 ^ (prefixWord ++ tailWord_2345480).sum := by decide
  have hdescent : baseEnd_2345480 < baseStart_2345480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345484 : List Nat := [2, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_2345484 : Nat := 118140960795 + 2345484 * 2 ^ 59
def prefixEnd_2345484 : Nat := 4983230072969 + 3 ^ 40 * 2345484 * 2
def baseEnd_2345484 : Nat := 267635702095601448169627

theorem tailTrace_2345484 : CollatzResearch.WordTrace tailWord_2345484 prefixEnd_2345484 267635702095601448169627 := by
  unfold tailWord_2345484
  simp only [CollatzResearch.WordTrace]
  refine ⟨42773414717359759810381753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57031219623146346413842337 42773414717359759810381753)
  ·
    refine ⟨32080061038019819857786315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42773414717359759810381753 32080061038019819857786315)
    ·
      refine ⟨48120091557029729786679473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32080061038019819857786315 48120091557029729786679473)
      ·
        refine ⟨36090068667772297340009605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48120091557029729786679473 36090068667772297340009605)
        ·
          refine ⟨6766887875207305751251801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36090068667772297340009605 6766887875207305751251801)
          ·
            refine ⟨5075165906405479313438851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6766887875207305751251801 5075165906405479313438851)
            ·
              refine ⟨7612748859608218970158277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5075165906405479313438851 7612748859608218970158277)
              ·
                refine ⟨1427390411176541056904677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7612748859608218970158277 1427390411176541056904677)
                ·
                  refine ⟨267635702095601448169627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427390411176541056904677 267635702095601448169627)
                  ·
                    rfl

theorem cell22_2345484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_2345484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345484 prefixEnd_2345484 := by exact prefixLift 2345484
  have htrace : WordTrace (prefixWord ++ tailWord_2345484) baseStart_2345484 baseEnd_2345484 := by
    simpa [prefixWord, tailWord_2345484, baseEnd_2345484] using wordTrace_append hprefix tailTrace_2345484
  have hstable : (prefixWord ++ tailWord_2345484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345484).length < 2 ^ (prefixWord ++ tailWord_2345484).sum := by decide
  have hdescent : baseEnd_2345484 < baseStart_2345484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345514 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2345514 : Nat := 118140960795 + 2345514 * 2 ^ 59
def prefixEnd_2345514 : Nat := 4983230072969 + 3 ^ 40 * 2345514 * 2
def baseEnd_2345514 : Nat := 802917375899894266258789

theorem tailTrace_2345514 : CollatzResearch.WordTrace tailWord_2345514 prefixEnd_2345514 802917375899894266258789 := by
  unfold tailWord_2345514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21386980906152708686088899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57031949083073889829570397 21386980906152708686088899)
  ·
    refine ⟨32080471359229063029133349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21386980906152708686088899 32080471359229063029133349)
    ·
      refine ⟨6015088379855449317962503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32080471359229063029133349 6015088379855449317962503)
      ·
        refine ⟨9022632569783173976943755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6015088379855449317962503 9022632569783173976943755)
        ·
          refine ⟨13533948854674760965415633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022632569783173976943755 13533948854674760965415633)
          ·
            refine ⟨10150461641006070724061725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13533948854674760965415633 10150461641006070724061725)
            ·
              refine ⟨3806423115377276521523147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10150461641006070724061725 3806423115377276521523147)
              ·
                refine ⟨5709634673065914782284721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806423115377276521523147 5709634673065914782284721)
                ·
                  refine ⟨4282226004799436086713541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5709634673065914782284721 4282226004799436086713541)
                  ·
                    refine ⟨802917375899894266258789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282226004799436086713541 802917375899894266258789)
                    ·
                      rfl

theorem cell22_2345514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2345514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345514 prefixEnd_2345514 := by exact prefixLift 2345514
  have htrace : WordTrace (prefixWord ++ tailWord_2345514) baseStart_2345514 baseEnd_2345514 := by
    simpa [prefixWord, tailWord_2345514, baseEnd_2345514] using wordTrace_append hprefix tailTrace_2345514
  have hstable : (prefixWord ++ tailWord_2345514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345514).length < 2 ^ (prefixWord ++ tailWord_2345514).sum := by decide
  have hdescent : baseEnd_2345514 < baseStart_2345514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345527 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 5, 3]
def baseStart_2345527 : Nat := 118140960795 + 2345527 * 2 ^ 59
def prefixEnd_2345527 : Nat := 4983230072969 + 3 ^ 40 * 2345527 * 2
def baseEnd_2345527 : Nat := 802921826065566565683749

theorem tailTrace_2345527 : CollatzResearch.WordTrace tailWord_2345527 prefixEnd_2345527 802921826065566565683749 := by
  unfold tailWord_2345527
  simp only [CollatzResearch.WordTrace]
  refine ⟨85548397773563737964578835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57032265182375825309719223 85548397773563737964578835)
  ·
    refine ⟨128322596660345606946868253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85548397773563737964578835 128322596660345606946868253)
    ·
      refine ⟨48120973747629602605075595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128322596660345606946868253 48120973747629602605075595)
      ·
        refine ⟨72181460621444403907613393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48120973747629602605075595 72181460621444403907613393)
        ·
          refine ⟨54136095466083302930710045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72181460621444403907613393 54136095466083302930710045)
          ·
            refine ⟨20301035799781238599016267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54136095466083302930710045 20301035799781238599016267)
            ·
              refine ⟨30451553699671857898524401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20301035799781238599016267 30451553699671857898524401)
              ·
                refine ⟨22838665274753893423893301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30451553699671857898524401 22838665274753893423893301)
                ·
                  refine ⟨2141124869508177508489997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22838665274753893423893301 2141124869508177508489997)
                  ·
                    refine ⟨802921826065566565683749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141124869508177508489997 802921826065566565683749)
                    ·
                      rfl

theorem cell22_2345527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_2345527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345527 prefixEnd_2345527 := by exact prefixLift 2345527
  have htrace : WordTrace (prefixWord ++ tailWord_2345527) baseStart_2345527 baseEnd_2345527 := by
    simpa [prefixWord, tailWord_2345527, baseEnd_2345527] using wordTrace_append hprefix tailTrace_2345527
  have hstable : (prefixWord ++ tailWord_2345527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345527).length < 2 ^ (prefixWord ++ tailWord_2345527).sum := by decide
  have hdescent : baseEnd_2345527 < baseStart_2345527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345557 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 5]
def baseStart_2345557 : Nat := 118140960795 + 2345557 * 2 ^ 59
def prefixEnd_2345557 : Nat := 4983230072969 + 3 ^ 40 * 2345557 * 2
def baseEnd_2345557 : Nat := 267644031892885495811219

theorem tailTrace_2345557 : CollatzResearch.WordTrace tailWord_2345557 prefixEnd_2345557 267644031892885495811219 := by
  unfold tailWord_2345557
  simp only [CollatzResearch.WordTrace]
  refine ⟨85549491963455053088170925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57032994642303368725447283 85549491963455053088170925)
  ·
    refine ⟨32081059486295644908064097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85549491963455053088170925 32081059486295644908064097)
    ·
      refine ⟨24060794614721733681048073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32081059486295644908064097 24060794614721733681048073)
      ·
        refine ⟨18045595961041300260786055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24060794614721733681048073 18045595961041300260786055)
        ·
          refine ⟨27068393941561950391179083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18045595961041300260786055 27068393941561950391179083)
          ·
            refine ⟨40602590912342925586768625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27068393941561950391179083 40602590912342925586768625)
            ·
              refine ⟨30451943184257194190076469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40602590912342925586768625 30451943184257194190076469)
              ·
                refine ⟨2854869673524111955319669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30451943184257194190076469 2854869673524111955319669)
                ·
                  refine ⟨267644031892885495811219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2854869673524111955319669 267644031892885495811219)
                  ·
                    rfl

theorem cell22_2345557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_2345557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345557 prefixEnd_2345557 := by exact prefixLift 2345557
  have htrace : WordTrace (prefixWord ++ tailWord_2345557) baseStart_2345557 baseEnd_2345557 := by
    simpa [prefixWord, tailWord_2345557, baseEnd_2345557] using wordTrace_append hprefix tailTrace_2345557
  have hstable : (prefixWord ++ tailWord_2345557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345557).length < 2 ^ (prefixWord ++ tailWord_2345557).sum := by decide
  have hdescent : baseEnd_2345557 < baseStart_2345557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345651 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 2, 3]
def baseStart_2345651 : Nat := 118140960795 + 2345651 * 2 ^ 59
def prefixEnd_2345651 : Nat := 4983230072969 + 3 ^ 40 * 2345651 * 2
def baseEnd_2345651 : Nat := 802964273799671575583369

theorem tailTrace_2345651 : CollatzResearch.WordTrace tailWord_2345651 prefixEnd_2345651 802964273799671575583369 := by
  unfold tailWord_2345651
  simp only [CollatzResearch.WordTrace]
  refine ⟨85552920425114507142092807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57035280283409671428061871 85552920425114507142092807)
  ·
    refine ⟨128329380637671760713139211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85552920425114507142092807 128329380637671760713139211)
    ·
      refine ⟨192494070956507641069708817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128329380637671760713139211 192494070956507641069708817)
      ·
        refine ⟨144370553217380730802281613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192494070956507641069708817 144370553217380730802281613)
        ·
          refine ⟨54138957456517774050855605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144370553217380730802281613 54138957456517774050855605)
          ·
            refine ⟨5075527261548541317267713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54138957456517774050855605 5075527261548541317267713)
            ·
              refine ⟨3806645446161405987950785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075527261548541317267713 3806645446161405987950785)
              ·
                refine ⟨2854984084621054490963089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3806645446161405987950785 2854984084621054490963089)
                ·
                  refine ⟨2141238063465790868222317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2854984084621054490963089 2141238063465790868222317)
                  ·
                    refine ⟨802964273799671575583369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141238063465790868222317 802964273799671575583369)
                    ·
                      rfl

theorem cell22_2345651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 3].length) (baseStart_2345651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345651 prefixEnd_2345651 := by exact prefixLift 2345651
  have htrace : WordTrace (prefixWord ++ tailWord_2345651) baseStart_2345651 baseEnd_2345651 := by
    simpa [prefixWord, tailWord_2345651, baseEnd_2345651] using wordTrace_append hprefix tailTrace_2345651
  have hstable : (prefixWord ++ tailWord_2345651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345651).length < 2 ^ (prefixWord ++ tailWord_2345651).sum := by decide
  have hdescent : baseEnd_2345651 < baseStart_2345651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345653 : List Nat := [1, 3, 3, 3, 1, 1, 4, 2, 4]
def baseStart_2345653 : Nat := 118140960795 + 2345653 * 2 ^ 59
def prefixEnd_2345653 : Nat := 4983230072969 + 3 ^ 40 * 2345653 * 2
def baseEnd_2345653 : Nat := 267654986146848079011121

theorem tailTrace_2345653 : CollatzResearch.WordTrace tailWord_2345653 prefixEnd_2345653 267654986146848079011121 := by
  unfold tailWord_2345653
  simp only [CollatzResearch.WordTrace]
  refine ⟨85552993371107261483665613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57035328914071507655777075 85552993371107261483665613)
  ·
    refine ⟨32082372514165223056374605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85552993371107261483665613 32082372514165223056374605)
    ·
      refine ⟨12030889692811958646140477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32082372514165223056374605 12030889692811958646140477)
      ·
        refine ⟨4511583634804484492302679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12030889692811958646140477 4511583634804484492302679)
        ·
          refine ⟨6767375452206726738454019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511583634804484492302679 6767375452206726738454019)
          ·
            refine ⟨10151063178310090107681029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6767375452206726738454019 10151063178310090107681029)
            ·
              refine ⟨1903324345933141895190193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10151063178310090107681029 1903324345933141895190193)
              ·
                refine ⟨1427493259449856421392645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903324345933141895190193 1427493259449856421392645)
                ·
                  refine ⟨267654986146848079011121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1427493259449856421392645 267654986146848079011121)
                  ·
                    rfl

theorem cell22_2345653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_2345653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345653 prefixEnd_2345653 := by exact prefixLift 2345653
  have htrace : WordTrace (prefixWord ++ tailWord_2345653) baseStart_2345653 baseEnd_2345653 := by
    simpa [prefixWord, tailWord_2345653, baseEnd_2345653] using wordTrace_append hprefix tailTrace_2345653
  have hstable : (prefixWord ++ tailWord_2345653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345653).length < 2 ^ (prefixWord ++ tailWord_2345653).sum := by decide
  have hdescent : baseEnd_2345653 < baseStart_2345653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345664 : List Nat := [2, 1, 1, 2, 4, 4, 1, 7]
def baseStart_2345664 : Nat := 118140960795 + 2345664 * 2 ^ 59
def prefixEnd_2345664 : Nat := 4983230072969 + 3 ^ 40 * 2345664 * 2
def baseEnd_2345664 : Nat := 89218747107260430556481

theorem tailTrace_2345664 : CollatzResearch.WordTrace tailWord_2345664 prefixEnd_2345664 89218747107260430556481 := by
  unfold tailWord_2345664
  simp only [CollatzResearch.WordTrace]
  refine ⟨42776697287033705181158023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57035596382711606908210697 42776697287033705181158023)
  ·
    refine ⟨64165045930550557771737035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42776697287033705181158023 64165045930550557771737035)
    ·
      refine ⟨96247568895825836657605553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64165045930550557771737035 96247568895825836657605553)
      ·
        refine ⟨72185676671869377493204165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96247568895825836657605553 72185676671869377493204165)
        ·
          refine ⟨13534814375975508279975781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72185676671869377493204165 13534814375975508279975781)
          ·
            refine ⟨2537777695495407802495459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13534814375975508279975781 2537777695495407802495459)
            ·
              refine ⟨3806666543243111703743189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537777695495407802495459 3806666543243111703743189)
              ·
                refine ⟨89218747107260430556481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3806666543243111703743189 89218747107260430556481)
                ·
                  rfl

theorem cell22_2345664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_2345664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345664 prefixEnd_2345664 := by exact prefixLift 2345664
  have htrace : WordTrace (prefixWord ++ tailWord_2345664) baseStart_2345664 baseEnd_2345664 := by
    simpa [prefixWord, tailWord_2345664, baseEnd_2345664] using wordTrace_append hprefix tailTrace_2345664
  have hstable : (prefixWord ++ tailWord_2345664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345664).length < 2 ^ (prefixWord ++ tailWord_2345664).sum := by decide
  have hdescent : baseEnd_2345664 < baseStart_2345664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345709 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 7]
def baseStart_2345709 : Nat := 118140960795 + 2345709 * 2 ^ 59
def prefixEnd_2345709 : Nat := 4983230072969 + 3 ^ 40 * 2345709 * 2
def baseEnd_2345709 : Nat := 267661376128326252544397

theorem tailTrace_2345709 : CollatzResearch.WordTrace tailWord_2345709 prefixEnd_2345709 267661376128326252544397 := by
  unfold tailWord_2345709
  simp only [CollatzResearch.WordTrace]
  refine ⟨85555035858904383047704181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57036690572602922031802787 85555035858904383047704181)
  ·
    refine ⟨8020784611772285910722267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85555035858904383047704181 8020784611772285910722267)
    ·
      refine ⟨12031176917658428866083401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8020784611772285910722267 12031176917658428866083401)
      ·
        refine ⟨9023382688243821649562551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12031176917658428866083401 9023382688243821649562551)
        ·
          refine ⟨13535074032365732474343827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9023382688243821649562551 13535074032365732474343827)
          ·
            refine ⟨20302611048548598711515741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13535074032365732474343827 20302611048548598711515741)
            ·
              refine ⟨7613479143205724516818403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20302611048548598711515741 7613479143205724516818403)
              ·
                refine ⟨11420218714808586775227605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613479143205724516818403 11420218714808586775227605)
                ·
                  refine ⟨267661376128326252544397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11420218714808586775227605 267661376128326252544397)
                  ·
                    rfl

theorem cell22_2345709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_2345709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345709 prefixEnd_2345709 := by exact prefixLift 2345709
  have htrace : WordTrace (prefixWord ++ tailWord_2345709) baseStart_2345709 baseEnd_2345709 := by
    simpa [prefixWord, tailWord_2345709, baseEnd_2345709] using wordTrace_append hprefix tailTrace_2345709
  have hstable : (prefixWord ++ tailWord_2345709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345709).length < 2 ^ (prefixWord ++ tailWord_2345709).sum := by decide
  have hdescent : baseEnd_2345709 < baseStart_2345709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345724 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2345724 : Nat := 118140960795 + 2345724 * 2 ^ 59
def prefixEnd_2345724 : Nat := 4983230072969 + 3 ^ 40 * 2345724 * 2
def baseEnd_2345724 : Nat := 802989263191523718508145

theorem tailTrace_2345724 : CollatzResearch.WordTrace tailWord_2345724 prefixEnd_2345724 802989263191523718508145 := by
  unfold tailWord_2345724
  simp only [CollatzResearch.WordTrace]
  refine ⟨42777791476925020304750113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57037055302566693739666817 42777791476925020304750113)
  ·
    refine ⟨32083343607693765228562585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42777791476925020304750113 32083343607693765228562585)
    ·
      refine ⟨24062507705770323921421939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32083343607693765228562585 24062507705770323921421939)
      ·
        refine ⟨36093761558655485882132909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24062507705770323921421939 36093761558655485882132909)
        ·
          refine ⟨13535160584495807205799841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36093761558655485882132909 13535160584495807205799841)
          ·
            refine ⟨10151370438371855404349881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13535160584495807205799841 10151370438371855404349881)
            ·
              refine ⟨7613527828778891553262411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10151370438371855404349881 7613527828778891553262411)
              ·
                refine ⟨11420291743168337329893617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7613527828778891553262411 11420291743168337329893617)
                ·
                  refine ⟨8565218807376252997420213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11420291743168337329893617 8565218807376252997420213)
                  ·
                    refine ⟨802989263191523718508145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8565218807376252997420213 802989263191523718508145)
                    ·
                      rfl

theorem cell22_2345724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2345724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345724 prefixEnd_2345724 := by exact prefixLift 2345724
  have htrace : WordTrace (prefixWord ++ tailWord_2345724) baseStart_2345724 baseEnd_2345724 := by
    simpa [prefixWord, tailWord_2345724, baseEnd_2345724] using wordTrace_append hprefix tailTrace_2345724
  have hstable : (prefixWord ++ tailWord_2345724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345724).length < 2 ^ (prefixWord ++ tailWord_2345724).sum := by decide
  have hdescent : baseEnd_2345724 < baseStart_2345724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345756 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_2345756 : Nat := 118140960795 + 2345756 * 2 ^ 59
def prefixEnd_2345756 : Nat := 4983230072969 + 3 ^ 40 * 2345756 * 2
def baseEnd_2345756 : Nat := 803000217445486301708047

theorem tailTrace_2345756 : CollatzResearch.WordTrace tailWord_2345756 prefixEnd_2345756 803000217445486301708047 := by
  unfold tailWord_2345756
  simp only [CollatzResearch.WordTrace]
  refine ⟨42778375044867055037332561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57037833393156073383110081 42778375044867055037332561)
  ·
    refine ⟨32083781283650291277999421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42778375044867055037332561 32083781283650291277999421)
    ·
      refine ⟨12031417981368859229249783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32083781283650291277999421 12031417981368859229249783)
      ·
        refine ⟨18047126972053288843874675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031417981368859229249783 18047126972053288843874675)
        ·
          refine ⟨27070690458079933265812013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047126972053288843874675 27070690458079933265812013)
          ·
            refine ⟨10151508921779974974679505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27070690458079933265812013 10151508921779974974679505)
            ·
              refine ⟨7613631691334981231009629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10151508921779974974679505 7613631691334981231009629)
              ·
                refine ⟨2855111884250617961628611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7613631691334981231009629 2855111884250617961628611)
                ·
                  refine ⟨4282667826375926942442917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855111884250617961628611 4282667826375926942442917)
                  ·
                    refine ⟨803000217445486301708047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282667826375926942442917 803000217445486301708047)
                    ·
                      rfl

theorem cell22_2345756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_2345756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345756 prefixEnd_2345756 := by exact prefixLift 2345756
  have htrace : WordTrace (prefixWord ++ tailWord_2345756) baseStart_2345756 baseEnd_2345756 := by
    simpa [prefixWord, tailWord_2345756, baseEnd_2345756] using wordTrace_append hprefix tailTrace_2345756
  have hstable : (prefixWord ++ tailWord_2345756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345756).length < 2 ^ (prefixWord ++ tailWord_2345756).sum := by decide
  have hdescent : baseEnd_2345756 < baseStart_2345756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345784 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2345784 : Nat := 118140960795 + 2345784 * 2 ^ 59
def prefixEnd_2345784 : Nat := 4983230072969 + 3 ^ 40 * 2345784 * 2
def baseEnd_2345784 : Nat := 803009802417703562007961

theorem tailTrace_2345784 : CollatzResearch.WordTrace tailWord_2345784 prefixEnd_2345784 803009802417703562007961 := by
  unfold tailWord_2345784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42778885666816335428342203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57038514222421780571122937 42778885666816335428342203)
  ·
    refine ⟨64168328500224503142513305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42778885666816335428342203 64168328500224503142513305)
    ·
      refine ⟨48126246375168377356884979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64168328500224503142513305 48126246375168377356884979)
      ·
        refine ⟨72189369562752566035327469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48126246375168377356884979 72189369562752566035327469)
        ·
          refine ⟨27071013586032212263247801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72189369562752566035327469 27071013586032212263247801)
          ·
            refine ⟨20303260189524159197435851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27071013586032212263247801 20303260189524159197435851)
            ·
              refine ⟨30454890284286238796153777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20303260189524159197435851 30454890284286238796153777)
              ·
                refine ⟨22841167713214679097115333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30454890284286238796153777 22841167713214679097115333)
                ·
                  refine ⟨4282718946227752330709125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22841167713214679097115333 4282718946227752330709125)
                  ·
                    refine ⟨803009802417703562007961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282718946227752330709125 803009802417703562007961)
                    ·
                      rfl

theorem cell22_2345784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2345784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345784 prefixEnd_2345784 := by exact prefixLift 2345784
  have htrace : WordTrace (prefixWord ++ tailWord_2345784) baseStart_2345784 baseEnd_2345784 := by
    simpa [prefixWord, tailWord_2345784, baseEnd_2345784] using wordTrace_append hprefix tailTrace_2345784
  have hstable : (prefixWord ++ tailWord_2345784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345784).length < 2 ^ (prefixWord ++ tailWord_2345784).sum := by decide
  have hdescent : baseEnd_2345784 < baseStart_2345784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345790 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_2345790 : Nat := 118140960795 + 2345790 * 2 ^ 59
def prefixEnd_2345790 : Nat := 4983230072969 + 3 ^ 40 * 2345790 * 2
def baseEnd_2345790 : Nat := 803011856340321546357943

theorem tailTrace_2345790 : CollatzResearch.WordTrace tailWord_2345790 prefixEnd_2345790 803011856340321546357943 := by
  unfold tailWord_2345790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694748771451366735175353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57038660114407289254268549 10694748771451366735175353)
  ·
    refine ⟨8021061578588525051381515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10694748771451366735175353 8021061578588525051381515)
    ·
      refine ⟨12031592367882787577072273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8021061578588525051381515 12031592367882787577072273)
      ·
        refine ⟨9023694275912090682804205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12031592367882787577072273 9023694275912090682804205)
        ·
          refine ⟨3383885353467034006051577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9023694275912090682804205 3383885353467034006051577)
          ·
            refine ⟨2537914015100275504538683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3383885353467034006051577 2537914015100275504538683)
            ·
              refine ⟨3806871022650413256808025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537914015100275504538683 3806871022650413256808025)
              ·
                refine ⟨2855153266987809942606019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3806871022650413256808025 2855153266987809942606019)
                ·
                  refine ⟨4282729900481714913909029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855153266987809942606019 4282729900481714913909029)
                  ·
                    refine ⟨803011856340321546357943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282729900481714913909029 803011856340321546357943)
                    ·
                      rfl

theorem cell22_2345790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_2345790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345790 prefixEnd_2345790 := by exact prefixLift 2345790
  have htrace : WordTrace (prefixWord ++ tailWord_2345790) baseStart_2345790 baseEnd_2345790 := by
    simpa [prefixWord, tailWord_2345790, baseEnd_2345790] using wordTrace_append hprefix tailTrace_2345790
  have hstable : (prefixWord ++ tailWord_2345790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345790).length < 2 ^ (prefixWord ++ tailWord_2345790).sum := by decide
  have hdescent : baseEnd_2345790 < baseStart_2345790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345801 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_2345801 : Nat := 118140960795 + 2345801 * 2 ^ 59
def prefixEnd_2345801 : Nat := 4983230072969 + 3 ^ 40 * 2345801 * 2
def baseEnd_2345801 : Nat := 803015621865121184332909

theorem tailTrace_2345801 : CollatzResearch.WordTrace tailWord_2345801 prefixEnd_2345801 803015621865121184332909 := by
  unfold tailWord_2345801
  simp only [CollatzResearch.WordTrace]
  refine ⟨85558391374571082760053257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57038927583047388506702171 85558391374571082760053257)
  ·
    refine ⟨64168793530928312070039943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85558391374571082760053257 64168793530928312070039943)
    ·
      refine ⟨96253190296392468105059915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64168793530928312070039943 96253190296392468105059915)
      ·
        refine ⟨144379785444588702157589873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96253190296392468105059915 144379785444588702157589873)
        ·
          refine ⟨108284839083441526618192405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144379785444588702157589873 108284839083441526618192405)
          ·
            refine ⟨5075851832036321560227769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108284839083441526618192405 5075851832036321560227769)
            ·
              refine ⟨3806888874027241170170827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075851832036321560227769 3806888874027241170170827)
              ·
                refine ⟨5710333311040861755256241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806888874027241170170827 5710333311040861755256241)
                ·
                  refine ⟨4282749983280646316442181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5710333311040861755256241 4282749983280646316442181)
                  ·
                    refine ⟨803015621865121184332909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4282749983280646316442181 803015621865121184332909)
                    ·
                      rfl

theorem cell22_2345801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_2345801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345801 prefixEnd_2345801 := by exact prefixLift 2345801
  have htrace : WordTrace (prefixWord ++ tailWord_2345801) baseStart_2345801 baseEnd_2345801 := by
    simpa [prefixWord, tailWord_2345801, baseEnd_2345801] using wordTrace_append hprefix tailTrace_2345801
  have hstable : (prefixWord ++ tailWord_2345801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345801).length < 2 ^ (prefixWord ++ tailWord_2345801).sum := by decide
  have hdescent : baseEnd_2345801 < baseStart_2345801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345820 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2345820 : Nat := 118140960795 + 2345820 * 2 ^ 59
def prefixEnd_2345820 : Nat := 4983230072969 + 3 ^ 40 * 2345820 * 2
def baseEnd_2345820 : Nat := 803022125953411468107851

theorem tailTrace_2345820 : CollatzResearch.WordTrace tailWord_2345820 prefixEnd_2345820 803022125953411468107851 := by
  unfold tailWord_2345820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42779542180751124502497457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57039389574334832669996609 42779542180751124502497457)
  ·
    refine ⟨32084656635563343376873093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42779542180751124502497457 32084656635563343376873093)
    ·
      refine ⟨6015873119168126883163705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32084656635563343376873093 6015873119168126883163705)
      ·
        refine ⟨4511904839376095162372779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6015873119168126883163705 4511904839376095162372779)
        ·
          refine ⟨6767857259064142743559169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4511904839376095162372779 6767857259064142743559169)
          ·
            refine ⟨5075892944298107057669377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6767857259064142743559169 5075892944298107057669377)
            ·
              refine ⟨3806919708223580293252033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075892944298107057669377 3806919708223580293252033)
              ·
                refine ⟨2855189781167685219939025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3806919708223580293252033 2855189781167685219939025)
                ·
                  refine ⟨2141392335875763914954269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2855189781167685219939025 2141392335875763914954269)
                  ·
                    refine ⟨803022125953411468107851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141392335875763914954269 803022125953411468107851)
                    ·
                      rfl

theorem cell22_2345820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2345820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345820 prefixEnd_2345820 := by exact prefixLift 2345820
  have htrace : WordTrace (prefixWord ++ tailWord_2345820) baseStart_2345820 baseEnd_2345820 := by
    simpa [prefixWord, tailWord_2345820, baseEnd_2345820] using wordTrace_append hprefix tailTrace_2345820
  have hstable : (prefixWord ++ tailWord_2345820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345820).length < 2 ^ (prefixWord ++ tailWord_2345820).sum := by decide
  have hdescent : baseEnd_2345820 < baseStart_2345820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345829 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2345829 : Nat := 118140960795 + 2345829 * 2 ^ 59
def prefixEnd_2345829 : Nat := 4983230072969 + 3 ^ 40 * 2345829 * 2
def baseEnd_2345829 : Nat := 803025206837338444632823

theorem tailTrace_2345829 : CollatzResearch.WordTrace tailWord_2345829 prefixEnd_2345829 803025206837338444632823 := by
  unfold tailWord_2345829
  simp only [CollatzResearch.WordTrace]
  refine ⟨85559412618469643542072541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57039608412313095694715027 85559412618469643542072541)
  ·
    refine ⟨32084779731926116328277203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85559412618469643542072541 32084779731926116328277203)
    ·
      refine ⟨48127169597889174492415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32084779731926116328277203 48127169597889174492415805)
      ·
        refine ⟨18047688599208440434655927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48127169597889174492415805 18047688599208440434655927)
        ·
          refine ⟨27071532898812660651983891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047688599208440434655927 27071532898812660651983891)
          ·
            refine ⟨40607299348218990977975837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27071532898812660651983891 40607299348218990977975837)
            ·
              refine ⟨15227737255582121616740939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40607299348218990977975837 15227737255582121616740939)
              ·
                refine ⟨22841605883373182425111409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15227737255582121616740939 22841605883373182425111409)
                ·
                  refine ⟨17131204412529886818833557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22841605883373182425111409 17131204412529886818833557)
                  ·
                    refine ⟨803025206837338444632823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17131204412529886818833557 803025206837338444632823)
                    ·
                      rfl

theorem cell22_2345829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2345829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345829 prefixEnd_2345829 := by exact prefixLift 2345829
  have htrace : WordTrace (prefixWord ++ tailWord_2345829) baseStart_2345829 baseEnd_2345829 := by
    simpa [prefixWord, tailWord_2345829, baseEnd_2345829] using wordTrace_append hprefix tailTrace_2345829
  have hstable : (prefixWord ++ tailWord_2345829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345829).length < 2 ^ (prefixWord ++ tailWord_2345829).sum := by decide
  have hdescent : baseEnd_2345829 < baseStart_2345829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345859 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_2345859 : Nat := 118140960795 + 2345859 * 2 ^ 59
def prefixEnd_2345859 : Nat := 4983230072969 + 3 ^ 40 * 2345859 * 2
def baseEnd_2345859 : Nat := 803035476450428366382731

theorem tailTrace_2345859 : CollatzResearch.WordTrace tailWord_2345859 prefixEnd_2345859 803035476450428366382731 := by
  unfold tailWord_2345859
  simp only [CollatzResearch.WordTrace]
  refine ⟨85560506808360958665664631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57040337872240639110443087 85560506808360958665664631)
  ·
    refine ⟨128340760212541437998496947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85560506808360958665664631 128340760212541437998496947)
    ·
      refine ⟨192511140318812156997745421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128340760212541437998496947 192511140318812156997745421)
      ·
        refine ⟨72191677619554558874154533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192511140318812156997745421 72191677619554558874154533)
        ·
          refine ⟨13535939553666479788903975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72191677619554558874154533 13535939553666479788903975)
          ·
            refine ⟨20303909330499719683355963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13535939553666479788903975 20303909330499719683355963)
            ·
              refine ⟨30455863995749579525033945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20303909330499719683355963 30455863995749579525033945)
              ·
                refine ⟨22841897996812184643775459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30455863995749579525033945 22841897996812184643775459)
                ·
                  refine ⟨34262846995218276965663189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22841897996812184643775459 34262846995218276965663189)
                  ·
                    refine ⟨803035476450428366382731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34262846995218276965663189 803035476450428366382731)
                    ·
                      rfl

theorem cell22_2345859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_2345859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345859 prefixEnd_2345859 := by exact prefixLift 2345859
  have htrace : WordTrace (prefixWord ++ tailWord_2345859) baseStart_2345859 baseEnd_2345859 := by
    simpa [prefixWord, tailWord_2345859, baseEnd_2345859] using wordTrace_append hprefix tailTrace_2345859
  have hstable : (prefixWord ++ tailWord_2345859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345859).length < 2 ^ (prefixWord ++ tailWord_2345859).sum := by decide
  have hdescent : baseEnd_2345859 < baseStart_2345859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345865 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 1, 3]
def baseStart_2345865 : Nat := 118140960795 + 2345865 * 2 ^ 59
def prefixEnd_2345865 : Nat := 4983230072969 + 3 ^ 40 * 2345865 * 2
def baseEnd_2345865 : Nat := 803037530373046350732713

theorem tailTrace_2345865 : CollatzResearch.WordTrace tailWord_2345865 prefixEnd_2345865 803037530373046350732713 := by
  unfold tailWord_2345865
  simp only [CollatzResearch.WordTrace]
  refine ⟨85560725646339221690383049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57040483764226147793588699 85560725646339221690383049)
  ·
    refine ⟨64170544234754416267787287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85560725646339221690383049 64170544234754416267787287)
    ·
      refine ⟨96255816352131624401680931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64170544234754416267787287 96255816352131624401680931)
      ·
        refine ⟨144383724528197436602521397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96255816352131624401680931 144383724528197436602521397)
        ·
          refine ⟨13535974174518509681486381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144383724528197436602521397 13535974174518509681486381)
          ·
            refine ⟨5075990315444441130557393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13535974174518509681486381 5075990315444441130557393)
            ·
              refine ⟨3806992736583330847918045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5075990315444441130557393 3806992736583330847918045)
              ·
                refine ⟨1427622276218749067969267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3806992736583330847918045 1427622276218749067969267)
                ·
                  refine ⟨2141433414328123601953901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427622276218749067969267 2141433414328123601953901)
                  ·
                    refine ⟨803037530373046350732713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141433414328123601953901 803037530373046350732713)
                    ·
                      rfl

theorem cell22_2345865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_2345865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345865 prefixEnd_2345865 := by exact prefixLift 2345865
  have htrace : WordTrace (prefixWord ++ tailWord_2345865) baseStart_2345865 baseEnd_2345865 := by
    simpa [prefixWord, tailWord_2345865, baseEnd_2345865] using wordTrace_append hprefix tailTrace_2345865
  have hstable : (prefixWord ++ tailWord_2345865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345865).length < 2 ^ (prefixWord ++ tailWord_2345865).sum := by decide
  have hdescent : baseEnd_2345865 < baseStart_2345865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345876 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2345876 : Nat := 118140960795 + 2345876 * 2 ^ 59
def prefixEnd_2345876 : Nat := 4983230072969 + 3 ^ 40 * 2345876 * 2
def baseEnd_2345876 : Nat := 803041295897845988707679

theorem tailTrace_2345876 : CollatzResearch.WordTrace tailWord_2345876 prefixEnd_2345876 803041295897845988707679 := by
  unfold tailWord_2345876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42780563424649685284516741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57040751232866247046022321 42780563424649685284516741)
  ·
    refine ⟨8021355642121815990846889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42780563424649685284516741 8021355642121815990846889)
    ·
      refine ⟨6016016731591361993135167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8021355642121815990846889 6016016731591361993135167)
      ·
        refine ⟨9024025097387042989702751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016016731591361993135167 9024025097387042989702751)
        ·
          refine ⟨13536037646080564484554127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9024025097387042989702751 13536037646080564484554127)
          ·
            refine ⟨20304056469120846726831191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13536037646080564484554127 20304056469120846726831191)
            ·
              refine ⟨30456084703681270090246787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20304056469120846726831191 30456084703681270090246787)
              ·
                refine ⟨45684127055521905135370181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30456084703681270090246787 45684127055521905135370181)
                ·
                  refine ⟨8565773822910357212881909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45684127055521905135370181 8565773822910357212881909)
                  ·
                    refine ⟨803041295897845988707679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8565773822910357212881909 803041295897845988707679)
                    ·
                      rfl

theorem cell22_2345876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2345876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345876 prefixEnd_2345876 := by exact prefixLift 2345876
  have htrace : WordTrace (prefixWord ++ tailWord_2345876) baseStart_2345876 baseEnd_2345876 := by
    simpa [prefixWord, tailWord_2345876, baseEnd_2345876] using wordTrace_append hprefix tailTrace_2345876
  have hstable : (prefixWord ++ tailWord_2345876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345876).length < 2 ^ (prefixWord ++ tailWord_2345876).sum := by decide
  have hdescent : baseEnd_2345876 < baseStart_2345876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345895 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 5]
def baseStart_2345895 : Nat := 118140960795 + 2345895 * 2 ^ 59
def prefixEnd_2345895 : Nat := 4983230072969 + 3 ^ 40 * 2345895 * 2
def baseEnd_2345895 : Nat := 267682599995378757494207

theorem tailTrace_2345895 : CollatzResearch.WordTrace tailWord_2345895 prefixEnd_2345895 267682599995378757494207 := by
  unfold tailWord_2345895
  simp only [CollatzResearch.WordTrace]
  refine ⟨85561819836230536813975139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57041213224153691209316759 85561819836230536813975139)
  ·
    refine ⟨128342729754345805220962709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85561819836230536813975139 128342729754345805220962709)
    ·
      refine ⟨6016065457234959619732627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128342729754345805220962709 6016065457234959619732627)
      ·
        refine ⟨9024098185852439429598941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6016065457234959619732627 9024098185852439429598941)
        ·
          refine ⟨3384036819694664786099603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9024098185852439429598941 3384036819694664786099603)
          ·
            refine ⟨5076055229541997179149405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384036819694664786099603 5076055229541997179149405)
            ·
              refine ⟨1903520711078248942181027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5076055229541997179149405 1903520711078248942181027)
              ·
                refine ⟨2855281066617373413271541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903520711078248942181027 2855281066617373413271541)
                ·
                  refine ⟨267682599995378757494207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2855281066617373413271541 267682599995378757494207)
                  ·
                    rfl

theorem cell22_2345895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 5].length) (baseStart_2345895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345895 prefixEnd_2345895 := by exact prefixLift 2345895
  have htrace : WordTrace (prefixWord ++ tailWord_2345895) baseStart_2345895 baseEnd_2345895 := by
    simpa [prefixWord, tailWord_2345895, baseEnd_2345895] using wordTrace_append hprefix tailTrace_2345895
  have hstable : (prefixWord ++ tailWord_2345895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345895).length < 2 ^ (prefixWord ++ tailWord_2345895).sum := by decide
  have hdescent : baseEnd_2345895 < baseStart_2345895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2345933 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2345933 : Nat := 118140960795 + 2345933 * 2 ^ 59
def prefixEnd_2345933 : Nat := 4983230072969 + 3 ^ 40 * 2345933 * 2
def baseEnd_2345933 : Nat := 803060808162716840032505

theorem tailTrace_2345933 : CollatzResearch.WordTrace tailWord_2345933 prefixEnd_2345933 803060808162716840032505 := by
  unfold tailWord_2345933
  simp only [CollatzResearch.WordTrace]
  refine ⟨85563205810092869303858453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57042137206728579535905635 85563205810092869303858453)
  ·
    refine ⟨4010775272348103248618365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85563205810092869303858453 4010775272348103248618365)
    ·
      refine ⟨1504040727130538718231887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4010775272348103248618365 1504040727130538718231887)
      ·
        refine ⟨2256061090695808077347831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504040727130538718231887 2256061090695808077347831)
        ·
          refine ⟨3384091636043712116021747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256061090695808077347831 3384091636043712116021747)
          ·
            refine ⟨5076137454065568174032621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384091636043712116021747 5076137454065568174032621)
            ·
              refine ⟨1903551545274588065262233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5076137454065568174032621 1903551545274588065262233)
              ·
                refine ⟨1427663658955941048946675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903551545274588065262233 1427663658955941048946675)
                ·
                  refine ⟨2141495488433911573420013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427663658955941048946675 2141495488433911573420013)
                  ·
                    refine ⟨803060808162716840032505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141495488433911573420013 803060808162716840032505)
                    ·
                      rfl

theorem cell22_2345933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2345933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2345933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2345933 prefixEnd_2345933 := by exact prefixLift 2345933
  have htrace : WordTrace (prefixWord ++ tailWord_2345933) baseStart_2345933 baseEnd_2345933 := by
    simpa [prefixWord, tailWord_2345933, baseEnd_2345933] using wordTrace_append hprefix tailTrace_2345933
  have hstable : (prefixWord ++ tailWord_2345933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2345933).length < 2 ^ (prefixWord ++ tailWord_2345933).sum := by decide
  have hdescent : baseEnd_2345933 < baseStart_2345933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2345933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346090 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2346090 : Nat := 118140960795 + 2346090 * 2 ^ 59
def prefixEnd_2346090 : Nat := 4983230072969 + 3 ^ 40 * 2346090 * 2
def baseEnd_2346090 : Nat := 803114552471220763857023

theorem tailTrace_2346090 : CollatzResearch.WordTrace tailWord_2346090 prefixEnd_2346090 803114552471220763857023 := by
  unfold tailWord_2346090
  simp only [CollatzResearch.WordTrace]
  refine ⟨21392233017631021279330931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57045954713682723411549149 21392233017631021279330931)
  ·
    refine ⟨32088349526446531918996397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21392233017631021279330931 32088349526446531918996397)
    ·
      refine ⟨12033131072417449469623649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32088349526446531918996397 12033131072417449469623649)
      ·
        refine ⟨9024848304313087102217737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12033131072417449469623649 9024848304313087102217737)
        ·
          refine ⟨6768636228234815326663303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9024848304313087102217737 6768636228234815326663303)
          ·
            refine ⟨10152954342352222989994955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6768636228234815326663303 10152954342352222989994955)
            ·
              refine ⟨15229431513528334484992433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10152954342352222989994955 15229431513528334484992433)
              ·
                refine ⟨11422073635146250863744325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15229431513528334484992433 11422073635146250863744325)
                ·
                  refine ⟨2141638806589922036952061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11422073635146250863744325 2141638806589922036952061)
                  ·
                    refine ⟨803114552471220763857023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141638806589922036952061 803114552471220763857023)
                    ·
                      rfl

theorem cell22_2346090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2346090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346090 prefixEnd_2346090 := by exact prefixLift 2346090
  have htrace : WordTrace (prefixWord ++ tailWord_2346090) baseStart_2346090 baseEnd_2346090 := by
    simpa [prefixWord, tailWord_2346090, baseEnd_2346090] using wordTrace_append hprefix tailTrace_2346090
  have hstable : (prefixWord ++ tailWord_2346090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346090).length < 2 ^ (prefixWord ++ tailWord_2346090).sum := by decide
  have hdescent : baseEnd_2346090 < baseStart_2346090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346105 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_2346105 : Nat := 118140960795 + 2346105 * 2 ^ 59
def prefixEnd_2346105 : Nat := 4983230072969 + 3 ^ 40 * 2346105 * 2
def baseEnd_2346105 : Nat := 803119687277765724731977

theorem tailTrace_2346105 : CollatzResearch.WordTrace tailWord_2346105 prefixEnd_2346105 803119687277765724731977 := by
  unfold tailWord_2346105
  simp only [CollatzResearch.WordTrace]
  refine ⟨85569479165469742679119769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57046319443646495119413179 85569479165469742679119769)
  ·
    refine ⟨64177109374102307009339827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85569479165469742679119769 64177109374102307009339827)
    ·
      refine ⟨96265664061153460514009741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64177109374102307009339827 96265664061153460514009741)
      ·
        refine ⟨36099624022932547692753653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96265664061153460514009741 36099624022932547692753653)
        ·
          refine ⟨3384339752149926346195655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36099624022932547692753653 3384339752149926346195655)
          ·
            refine ⟨5076509628224889519293483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384339752149926346195655 5076509628224889519293483)
            ·
              refine ⟨7614764442337334278940225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5076509628224889519293483 7614764442337334278940225)
              ·
                refine ⟨5711073331753000709205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7614764442337334278940225 5711073331753000709205169)
                ·
                  refine ⟨4283304998814750531903877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5711073331753000709205169 4283304998814750531903877)
                  ·
                    refine ⟨803119687277765724731977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283304998814750531903877 803119687277765724731977)
                    ·
                      rfl

theorem cell22_2346105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_2346105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346105 prefixEnd_2346105 := by exact prefixLift 2346105
  have htrace : WordTrace (prefixWord ++ tailWord_2346105) baseStart_2346105 baseEnd_2346105 := by
    simpa [prefixWord, tailWord_2346105, baseEnd_2346105] using wordTrace_append hprefix tailTrace_2346105
  have hstable : (prefixWord ++ tailWord_2346105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346105).length < 2 ^ (prefixWord ++ tailWord_2346105).sum := by decide
  have hdescent : baseEnd_2346105 < baseStart_2346105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346120 : List Nat := [2, 1, 3, 4, 2, 1, 2, 7]
def baseStart_2346120 : Nat := 118140960795 + 2346120 * 2 ^ 59
def prefixEnd_2346120 : Nat := 4983230072969 + 3 ^ 40 * 2346120 * 2
def baseEnd_2346120 : Nat := 89236091342701187289659

theorem tailTrace_2346120 : CollatzResearch.WordTrace tailWord_2346120 prefixEnd_2346120 89236091342701187289659 := by
  unfold tailWord_2346120
  simp only [CollatzResearch.WordTrace]
  refine ⟨42785013130207700120457907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57046684173610266827277209 42785013130207700120457907)
  ·
    refine ⟨64177519695311550180686861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42785013130207700120457907 64177519695311550180686861)
    ·
      refine ⟨24066569885741831317757573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64177519695311550180686861 24066569885741831317757573)
      ·
        refine ⟨4512481853576593372079545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24066569885741831317757573 4512481853576593372079545)
        ·
          refine ⟨3384361390182445029059659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4512481853576593372079545 3384361390182445029059659)
          ·
            refine ⟨5076542085273667543589489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3384361390182445029059659 5076542085273667543589489)
            ·
              refine ⟨3807406563955250657692117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5076542085273667543589489 3807406563955250657692117)
              ·
                refine ⟨89236091342701187289659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3807406563955250657692117 89236091342701187289659)
                ·
                  rfl

theorem cell22_2346120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_2346120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346120 prefixEnd_2346120 := by exact prefixLift 2346120
  have htrace : WordTrace (prefixWord ++ tailWord_2346120) baseStart_2346120 baseEnd_2346120 := by
    simpa [prefixWord, tailWord_2346120, baseEnd_2346120] using wordTrace_append hprefix tailTrace_2346120
  have hstable : (prefixWord ++ tailWord_2346120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346120).length < 2 ^ (prefixWord ++ tailWord_2346120).sum := by decide
  have hdescent : baseEnd_2346120 < baseStart_2346120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346169 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_2346169 : Nat := 118140960795 + 2346169 * 2 ^ 59
def prefixEnd_2346169 : Nat := 4983230072969 + 3 ^ 40 * 2346169 * 2
def baseEnd_2346169 : Nat := 803141595785690891131781

theorem tailTrace_2346169 : CollatzResearch.WordTrace tailWord_2346169 prefixEnd_2346169 803141595785690891131781 := by
  unfold tailWord_2346169
  simp only [CollatzResearch.WordTrace]
  refine ⟨85571813437237881609449561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57047875624825254406299707 85571813437237881609449561)
  ·
    refine ⟨64178860077928411207087171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85571813437237881609449561 64178860077928411207087171)
    ·
      refine ⟨96268290116892616810630757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64178860077928411207087171 96268290116892616810630757)
      ·
        refine ⟨18050304396917365651993267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96268290116892616810630757 18050304396917365651993267)
        ·
          refine ⟨27075456595376048477989901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18050304396917365651993267 27075456595376048477989901)
          ·
            refine ⟨10153296223266018179246213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27075456595376048477989901 10153296223266018179246213)
            ·
              refine ⟨1903743041862378408608665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10153296223266018179246213 1903743041862378408608665)
              ·
                refine ⟨1427807281396783806456499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1903743041862378408608665 1427807281396783806456499)
                ·
                  refine ⟨2141710922095175709684749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1427807281396783806456499 2141710922095175709684749)
                  ·
                    refine ⟨803141595785690891131781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2141710922095175709684749 803141595785690891131781)
                    ·
                      rfl

theorem cell22_2346169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_2346169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346169 prefixEnd_2346169 := by exact prefixLift 2346169
  have htrace : WordTrace (prefixWord ++ tailWord_2346169) baseStart_2346169 baseEnd_2346169 := by
    simpa [prefixWord, tailWord_2346169, baseEnd_2346169] using wordTrace_append hprefix tailTrace_2346169
  have hstable : (prefixWord ++ tailWord_2346169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346169).length < 2 ^ (prefixWord ++ tailWord_2346169).sum := by decide
  have hdescent : baseEnd_2346169 < baseStart_2346169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346212 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_2346212 : Nat := 118140960795 + 2346212 * 2 ^ 59
def prefixEnd_2346212 : Nat := 4983230072969 + 3 ^ 40 * 2346212 * 2
def baseEnd_2346212 : Nat := 803156315564453112306649

theorem tailTrace_2346212 : CollatzResearch.WordTrace tailWord_2346212 prefixEnd_2346212 803156315564453112306649 := by
  unfold tailWord_2346212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42786690888041049976632445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57048921184054733302176593 42786690888041049976632445)
  ·
    refine ⟨16045009083015393741237167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42786690888041049976632445 16045009083015393741237167)
    ·
      refine ⟨24067513624523090611855751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16045009083015393741237167 24067513624523090611855751)
      ·
        refine ⟨36101270436784635917783627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24067513624523090611855751 36101270436784635917783627)
        ·
          refine ⟨54151905655176953876675441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36101270436784635917783627 54151905655176953876675441)
          ·
            refine ⟨40613929241382715407506581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54151905655176953876675441 40613929241382715407506581)
            ·
              refine ⟨1903777933189814784726871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40613929241382715407506581 1903777933189814784726871)
              ·
                refine ⟨2855666899784722177090307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1903777933189814784726871 2855666899784722177090307)
                ·
                  refine ⟨4283500349677083265635461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2855666899784722177090307 4283500349677083265635461)
                  ·
                    refine ⟨803156315564453112306649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4283500349677083265635461 803156315564453112306649)
                    ·
                      rfl

theorem cell22_2346212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_2346212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346212 prefixEnd_2346212 := by exact prefixLift 2346212
  have htrace : WordTrace (prefixWord ++ tailWord_2346212) baseStart_2346212 baseEnd_2346212 := by
    simpa [prefixWord, tailWord_2346212, baseEnd_2346212] using wordTrace_append hprefix tailTrace_2346212
  have hstable : (prefixWord ++ tailWord_2346212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346212).length < 2 ^ (prefixWord ++ tailWord_2346212).sum := by decide
  have hdescent : baseEnd_2346212 < baseStart_2346212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346272 : List Nat := [2, 1, 1, 5, 4, 1, 8]
def baseStart_2346272 : Nat := 118140960795 + 2346272 * 2 ^ 59
def prefixEnd_2346272 : Nat := 4983230072969 + 3 ^ 40 * 2346272 * 2
def baseEnd_2346272 : Nat := 29747290918171590955795

theorem tailTrace_2346272 : CollatzResearch.WordTrace tailWord_2346272 prefixEnd_2346272 29747290918171590955795 := by
  unfold tailWord_2346272
  simp only [CollatzResearch.WordTrace]
  refine ⟨42787785077932365100224535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57050380103909820133632713 42787785077932365100224535)
  ·
    refine ⟨64181677616898547650336803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42787785077932365100224535 64181677616898547650336803)
    ·
      refine ⟨96272516425347821475505205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64181677616898547650336803 96272516425347821475505205)
      ·
        refine ⟨9025548414876358263328613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96272516425347821475505205 9025548414876358263328613)
        ·
          refine ⟨1692290327789317174374115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9025548414876358263328613 1692290327789317174374115)
          ·
            refine ⟨2538435491683975761561173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1692290327789317174374115 2538435491683975761561173)
            ·
              refine ⟨29747290918171590955795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2538435491683975761561173 29747290918171590955795)
              ·
                rfl

theorem cell22_2346272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 8].length) (baseStart_2346272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346272 prefixEnd_2346272 := by exact prefixLift 2346272
  have htrace : WordTrace (prefixWord ++ tailWord_2346272) baseStart_2346272 baseEnd_2346272 := by
    simpa [prefixWord, tailWord_2346272, baseEnd_2346272] using wordTrace_append hprefix tailTrace_2346272
  have hstable : (prefixWord ++ tailWord_2346272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346272).length < 2 ^ (prefixWord ++ tailWord_2346272).sum := by decide
  have hdescent : baseEnd_2346272 < baseStart_2346272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346435 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 7]
def baseStart_2346435 : Nat := 118140960795 + 2346435 * 2 ^ 59
def prefixEnd_2346435 : Nat := 4983230072969 + 3 ^ 40 * 2346435 * 2
def baseEnd_2346435 : Nat := 267744217673918287993655

theorem tailTrace_2346435 : CollatzResearch.WordTrace tailWord_2346435 prefixEnd_2346435 267744217673918287993655 := by
  unfold tailWord_2346435
  simp only [CollatzResearch.WordTrace]
  refine ⟨85581515254274209038632759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57054343502849472692421839 85581515254274209038632759)
  ·
    refine ⟨128372272881411313557949139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85581515254274209038632759 128372272881411313557949139)
    ·
      refine ⟨192558409322116970336923709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128372272881411313557949139 192558409322116970336923709)
      ·
        refine ⟨72209403495793863876346391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 192558409322116970336923709 72209403495793863876346391)
        ·
          refine ⟨108314105243690795814519587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72209403495793863876346391 108314105243690795814519587)
          ·
            refine ⟨162471157865536193721779381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108314105243690795814519587 162471157865536193721779381)
            ·
              refine ⟨15231671049894018161416817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162471157865536193721779381 15231671049894018161416817)
              ·
                refine ⟨11423753287420513621062613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15231671049894018161416817 11423753287420513621062613)
                ·
                  refine ⟨267744217673918287993655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11423753287420513621062613 267744217673918287993655)
                  ·
                    rfl

theorem cell22_2346435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_2346435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346435 prefixEnd_2346435 := by exact prefixLift 2346435
  have htrace : WordTrace (prefixWord ++ tailWord_2346435) baseStart_2346435 baseEnd_2346435 := by
    simpa [prefixWord, tailWord_2346435, baseEnd_2346435] using wordTrace_append hprefix tailTrace_2346435
  have hstable : (prefixWord ++ tailWord_2346435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346435).length < 2 ^ (prefixWord ++ tailWord_2346435).sum := by decide
  have hdescent : baseEnd_2346435 < baseStart_2346435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346469 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 5]
def baseStart_2346469 : Nat := 118140960795 + 2346469 * 2 ^ 59
def prefixEnd_2346469 : Nat := 4983230072969 + 3 ^ 40 * 2346469 * 2
def baseEnd_2346469 : Nat := 267748097305530036210287

theorem tailTrace_2346469 : CollatzResearch.WordTrace tailWord_2346469 prefixEnd_2346469 267748097305530036210287 := by
  unfold tailWord_2346469
  simp only [CollatzResearch.WordTrace]
  refine ⟨85582755336151032845370461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57055170224100688563580307 85582755336151032845370461)
  ·
    refine ⟨32093533251056637317013923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85582755336151032845370461 32093533251056637317013923)
    ·
      refine ⟨48140299876584955975520885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32093533251056637317013923 48140299876584955975520885)
      ·
        refine ⟨4513153113429839622705083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48140299876584955975520885 4513153113429839622705083)
        ·
          refine ⟨6769729670144759434057625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4513153113429839622705083 6769729670144759434057625)
          ·
            refine ⟨5077297252608569575543219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6769729670144759434057625 5077297252608569575543219)
            ·
              refine ⟨7615945878912854363314829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5077297252608569575543219 7615945878912854363314829)
              ·
                refine ⟨2855979704592320386243061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7615945878912854363314829 2855979704592320386243061)
                ·
                  refine ⟨267748097305530036210287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2855979704592320386243061 267748097305530036210287)
                  ·
                    rfl

theorem cell22_2346469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_2346469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346469 prefixEnd_2346469 := by exact prefixLift 2346469
  have htrace : WordTrace (prefixWord ++ tailWord_2346469) baseStart_2346469 baseEnd_2346469 := by
    simpa [prefixWord, tailWord_2346469, baseEnd_2346469] using wordTrace_append hprefix tailTrace_2346469
  have hstable : (prefixWord ++ tailWord_2346469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346469).length < 2 ^ (prefixWord ++ tailWord_2346469).sum := by decide
  have hdescent : baseEnd_2346469 < baseStart_2346469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2346527 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2346527 : Nat := 118140960795 + 2346527 * 2 ^ 59
def prefixEnd_2346527 : Nat := 4983230072969 + 3 ^ 40 * 2346527 * 2
def baseEnd_2346527 : Nat := 803264146501897290680683

theorem tailTrace_2346527 : CollatzResearch.WordTrace tailWord_2346527 prefixEnd_2346527 803264146501897290680683 := by
  unfold tailWord_2346527
  simp only [CollatzResearch.WordTrace]
  refine ⟨85584870769940908750981835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57056580513293939167321223 85584870769940908750981835)
  ·
    refine ⟨128377306154911363126472753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85584870769940908750981835 128377306154911363126472753)
    ·
      refine ⟨96282979616183522344854565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128377306154911363126472753 96282979616183522344854565)
      ·
        refine ⟨18053058678034410439660231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96282979616183522344854565 18053058678034410439660231)
        ·
          refine ⟨27079588017051615659490347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18053058678034410439660231 27079588017051615659490347)
          ·
            refine ⟨40619382025577423489235521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27079588017051615659490347 40619382025577423489235521)
            ·
              refine ⟨30464536519183067616926641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40619382025577423489235521 30464536519183067616926641)
              ·
                refine ⟨22848402389387300712694981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30464536519183067616926641 22848402389387300712694981)
                ·
                  refine ⟨4284075448010118883630309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22848402389387300712694981 4284075448010118883630309)
                  ·
                    refine ⟨803264146501897290680683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4284075448010118883630309 803264146501897290680683)
                    ·
                      rfl

theorem cell22_2346527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2346527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2346527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2346527 prefixEnd_2346527 := by exact prefixLift 2346527
  have htrace : WordTrace (prefixWord ++ tailWord_2346527) baseStart_2346527 baseEnd_2346527 := by
    simpa [prefixWord, tailWord_2346527, baseEnd_2346527] using wordTrace_append hprefix tailTrace_2346527
  have hstable : (prefixWord ++ tailWord_2346527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2346527).length < 2 ^ (prefixWord ++ tailWord_2346527).sum := by decide
  have hdescent : baseEnd_2346527 < baseStart_2346527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2346527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
